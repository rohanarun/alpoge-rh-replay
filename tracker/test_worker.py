import contextlib
import gzip
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import Mock, patch

import replay_evidence as evidence
import tasks
import warm
import worker
import worker_build
import worker_github


class LostReply(RuntimeError):
    pass


class FakeGitHub:
    owner = 'volunteer'
    fork = 'volunteer/evidence'

    def __init__(self):
        self.issues = {}
        self.history = {}
        self.posts = []
        self.cut = None
        self.conflicts = set()
        self.closed = []

    def snapshot(self):
        return list(self.issues.values())

    def watch(self, numbers):
        return [self.issues[n] for n in numbers]

    def find_claim(self, marker):
        return next((i for i in self.snapshot() if marker in i['body']), None)

    def issue(self, n):
        return self.issues[n]

    def comments(self, n):
        return self.history[n]

    def claim(self, target, marker):
        n = len(self.issues) + 1
        issue = dict(number=n, title='Claim ' + target, state='open', body=marker,
                     labels=[{'name': 'claim-granted'}], user={'login': self.owner}, comments=1)
        self.issues[n] = issue
        self.history[n] = [dict(user=dict(login='github-actions[bot]'), body=f'Granted `{target}`.')]
        if target in self.conflicts:
            issue['labels'] = [{'name': 'claim-conflict'}]
            self.history[n] = [dict(user=dict(login='github-actions[bot]'), body='No grant.')]
        if self.cut == 'claim':
            raise LostReply('created claim')
        return issue

    def publish_assets(self, n, target, files):
        if self.cut == 'build':
            raise LostReply('completed build')
        return ' '.join(f.name for f in files)

    def submit(self, n, body):
        url = f'https://example.test/issues/{n}#comment'
        self.posts.append(n)
        self.history[n].append(dict(user={'login': self.owner}, body=body, html_url=url))
        self.issues[n]['comments'] += 1
        if self.cut == 'submit':
            raise LostReply('submitted comment')
        return url

    def close(self, n):
        self.closed.append(n)
        self.issues[n]['state'] = 'closed'


class WorkerTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.gh = FakeGitHub()
        self.tracker = self.root / 'tracker'
        self.tracker.mkdir()
        self.project = self.root / 'lean'
        src = self.project / 'src/Fixture'
        src.mkdir(parents=True)
        self.summary = json.loads((tasks.base / 'summary.json').read_text())
        shutil.copy(tasks.base.parent / 'parts.sha256', self.root)
        self.rows = []
        for i in range(20):
            name = f'Mod{i}'
            f = src / (name + '.lean')
            f.write_text(f'theorem fixture{i} : True := True.intro\n')
            self.rows.append(dict(id=f'M{i+1:06}', packet='P0001', module='Fixture.' + name,
                                  depth=0, state='open', imports=[], source_sha256=tasks.digest(f)))
        with gzip.open(self.tracker / 'modules.jsonl.gz', 'wt') as stream:
            for row in self.rows:
                print(json.dumps(row), file=stream)
        (self.tracker / 'summary.json').write_text(json.dumps(self.summary))
        self.assignments = self.root / 'ids'
        self.assignments.write_text('\n'.join(r['id'] for r in self.rows))
        self.build_count = 0
        change = patch.object(tasks, 'base', self.tracker)
        change.start()
        self.addCleanup(change.stop)

    def artifacts(self, target, number, platform='aarch64-unknown-linux-gnu'):
        out = self.root / str(number)
        if out.exists():
            return out
        self.build_count += 1
        out.mkdir()
        row = self.rows[int(target[1:]) - 1]
        name = row['module']
        log = out / 'build.log'
        log.write_text(f'✔ [1/1] Built {name} (1s)\nBuild completed successfully (1 job).\n')
        bundle = out / 'targets.tar.gz'
        obj = self.root / 'sample.olean'
        obj.write_text(name)
        with tarfile.open(bundle, 'w:gz') as tar:
            tar.add(obj, arcname='lib/lean/' + name.replace('.', '/') + '.olean')
        record = dict(tasks=[target], command=['lake', 'build', '+' + name + ':olean'], exit_code=0,
                      elapsed_seconds=1, objects={target: tasks.digest(obj)}, log_sha256=tasks.digest(log),
                      bundle_sha256=tasks.digest(bundle), inputs_manifest_sha256=tasks.digest(self.root / 'parts.sha256'),
                      toolchain=f"Lean (version 4.33.1, {platform}, commit {self.summary['lean_commit']}, Release)",
                      mathlib=self.summary['mathlib_commit'])
        (out / 'receipt.json').write_text(json.dumps(record))
        return out

    def launch(self, builder, jobs=1):
        argv = ['worker.py', str(self.assignments), str(self.root / 'state'), '--container', 'fixture',
                '--fork', self.gh.fork, '--jobs', str(jobs), '--poll', '1']
        adapter = Mock(side_effect=builder)
        adapter.preflight.return_value = dict(**evidence.pins(), platform='fixture')
        with patch.object(sys, 'argv', argv), patch.object(worker, 'GitHub', return_value=self.gh), \
                patch.object(worker, 'DockerBuilder', return_value=adapter), contextlib.redirect_stdout(io.StringIO()):
            return worker.main()

    def test_20_assignments_recover_build(self):
        self.gh.cut = 'build'
        with self.assertRaises(LostReply):
            self.launch(self.artifacts)
        self.assertEqual(self.build_count, 1)
        self.gh.cut = None
        self.assertEqual(self.launch(self.artifacts), 0)
        self.assertEqual(self.launch(self.artifacts), 0)
        self.assertEqual((len(self.gh.issues), self.build_count, self.gh.posts),
                         (20, 20, list(range(1, 21))))

    def test_failed_open_grant_keeps_its_slot_until_released(self):
        self.assignments.write_text('M000001 M000002')
        def fail_first(target, number):
            if number == 1:
                raise ValueError('failed build')
            return self.artifacts(target, number)
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(self.launch(fail_first), 1)
        self.assertEqual(len(self.gh.issues), 1)
        self.gh.issues[1]['state'] = 'closed'
        self.assertEqual(self.launch(fail_first), 1)
        self.assertEqual(self.gh.posts, [2])

    def test_reconcile_lost_github_replies(self):
        self.assignments.write_text('M000001')
        for cut in ['claim', 'submit']:
            self.gh.cut = cut
            with self.assertRaises(LostReply):
                self.launch(self.artifacts)
        self.gh.cut = None
        self.assertEqual(self.launch(self.artifacts), 0)
        self.assertEqual((len(self.gh.issues), self.build_count, self.gh.posts), (1, 1, [1]))

    def test_grant_requires_owner_label_and_bot(self):
        issue = self.gh.claim('M000001', 'marker')
        for label, author, body, owner, expected in [
            (False, 'github-actions[bot]', 'Granted `M000001`.', 'volunteer', 'pending'),
            (True, 'volunteer', 'Granted `M000001`.', 'volunteer', 'pending'),
            (True, 'github-actions[bot]', 'Granted `M000002`.', 'volunteer', 'pending'),
            (True, 'github-actions[bot]', 'Granted `M000001`.', 'another', 'wrong claim'),
        ]:
            issue['labels'] = [{'name': 'claim-granted'}] if label else []
            state, _ = worker.inspect_grant(issue, [dict(user={'login': author}, body=body)], 'M000001', owner)
            self.assertEqual(state, expected)

    def test_close_own_conflicting_claim_once(self):
        self.assignments.write_text('M000001 M000002')
        self.gh.conflicts.add('M000001')
        with contextlib.redirect_stderr(io.StringIO()):
            self.launch(self.artifacts)
            self.launch(self.artifacts)
        self.assertEqual((self.gh.closed, self.gh.posts), ([1], [2]))

    def test_verify_architectures_and_reject_corruption(self):
        row = self.rows[0]
        rows = {row['module']: row}
        for n, arch in enumerate(('aarch64-unknown-linux-gnu', 'x86_64-unknown-linux-gnu')):
            out = self.artifacts(row['id'], n, arch)
            result = evidence.verify(out, [row], rows)
            self.assertEqual(result['identity']['platform'], arch)
            bundle = out / 'targets.tar.gz'
            with tarfile.open(bundle, 'w:gz') as tar:
                member = tarfile.TarInfo('lib/lean/Fixture/Mod0.olean')
                member.size = 4
                tar.addfile(member, io.BytesIO(b'fake'))
            rec = json.loads((out / 'receipt.json').read_text())
            rec['bundle_sha256'] = tasks.digest(bundle)
            (out / 'receipt.json').write_text(json.dumps(rec))
            with self.assertRaisesRegex(ValueError, 'Bundled object mismatch'):
                evidence.verify(out, [row], rows)

    def test_cached_footer_alone_cannot_be_published(self):
        self.assignments.write_text('M000001')
        out = self.artifacts('M000001', 1)
        log = out / 'build.log'
        log.write_text('All targets up-to-date (2 jobs).\n')
        receipt = out / 'receipt.json'
        record = json.loads(receipt.read_text())
        record['log_sha256'] = tasks.digest(log)
        receipt.write_text(json.dumps(record))
        with patch.object(self.gh, 'publish_assets') as upload:
            self.assertEqual(self.launch(self.artifacts), 1)
            upload.assert_not_called()
        self.assertEqual(self.gh.posts, [])
        row = self.rows[0]
        sidecar = dict(receipt_sha256=tasks.digest(receipt), command=evidence.replay_command([row]),
                       exit_code=0, transcript='replaying Fixture.Mod00\n')
        path = out / evidence.REPLAY_FILE
        path.write_text(json.dumps(sidecar))
        with self.assertRaisesRegex(ValueError, 'Missing kernel replay line'):
            evidence.verify(out, [row], {row['module']: row})
        sidecar.update(receipt_sha256='0'*64, transcript='replaying Fixture.Mod0\n')
        path.write_text(json.dumps(sidecar))
        with self.assertRaisesRegex(ValueError, 'different receipt'):
            evidence.verify(out, [row], {row['module']: row})

    def test_docker_builder_copies_cached_target_record_on_first_run_and_resume(self):
        row = self.rows[0]
        target = row['id']
        remote = self.artifacts(target, 1)
        (remote / 'build.log').write_text('All targets up-to-date (2 jobs).\n')
        (remote / evidence.REPLAY_FILE).write_text('kernel record')
        controller = self.root / 'controller'
        controller.mkdir()
        mirror = controller / '1'
        args = Mock(container='fixture', container_repo='/repo', checkout='/project',
                    receipts='/receipts', retry=[])
        builder = worker.DockerBuilder(args, controller, {target: [row]})

        def docker(cmd, **kwargs):
            if cmd[1] == 'cp':
                shutil.copyfile(remote / Path(cmd[2]).name, cmd[3])

        with patch.object(subprocess, 'run', side_effect=docker) as run:
            self.assertEqual(builder(target, 1), mirror)
            self.assertEqual((mirror / evidence.REPLAY_FILE).read_text(), 'kernel record')
            (mirror / evidence.REPLAY_FILE).unlink()
            run.reset_mock()
            self.assertEqual(builder(target, 1), mirror)
            copied = [c.args[0][2] for c in run.call_args_list if c.args[0][1] == 'cp']
            self.assertEqual(copied, [f'fixture:/receipts/{target}-1/{evidence.REPLAY_FILE}'])
            run.reset_mock()
            builder(target, 1)
            run.assert_not_called()

    def test_warm_plans_disjoint_closures(self):
        rows = self.rows[:8]
        a, b, c, d, e, f, g, h = [r['id'] for r in rows]
        for row, deps, depth in zip(rows, [[], [], [a], [b], [b], [c], [c], [d]], [0, 0, 1, 1, 1, 2, 2, 2]):
            row.update(imports=deps, depth=depth)
        rows[1]['state'] = 'build-observed'
        order = lambda busy: [(r['id'], cost) for r, cost, _ in warm.suggestions(
            rows, busy, {a}, {e}, 20, 2)]
        self.assertEqual(order({g}), [(c, 1), (d, 2)])
        self.assertEqual(order({b, g}), [(c, 1)])
        self.assignments.write_text('M000001 P0001')
        with self.assertRaisesRegex(ValueError, 'overlapping'):
            worker.plan(self.assignments, self.rows)

    def test_release_resume_only_uploads_missing_assets_and_checks_all_digests(self):
        out = self.artifacts('M000001', 1)
        files = [out / name for name in worker.FILES]
        assets = [dict(name=p.name, state='uploaded', digest='sha256:' + tasks.digest(p),
                       browser_download_url='https://example.test/' + p.name) for p in files]
        github = object.__new__(worker_github.GitHub)
        github.fork = 'volunteer/evidence'
        present = subprocess.CompletedProcess([], 0, json.dumps({'assets': assets[:1]}), '')
        with patch.object(subprocess, 'run', side_effect=[present, None]) as run, \
                patch.object(worker_github, 'api', return_value={'assets': assets}):
            links = github.publish_assets(7, 'M000001', files)
            self.assertIn('targets.tar.gz', links)
            self.assertEqual(run.call_args_list[1].args[0][-2:], files[1:])
        assets[0]['digest'] = 'sha256:' + '0' * 64
        existing = subprocess.CompletedProcess([], 0, json.dumps({'assets': assets}), '')
        with patch.object(subprocess, 'run', return_value=existing) as run:
            with self.assertRaisesRegex(ValueError, 'Published digest mismatch'):
                github.publish_assets(7, 'M000001', files)
            run.assert_called_once()

    def test_receiver_checks_installed_objects_and_platform_before_lake(self):
        out = self.artifacts('M000001', 1)
        build = self.project / '.lake/build/lib/lean/Fixture'
        build.mkdir(parents=True)
        installed = build / 'Mod0.olean'
        installed.write_text('wrong')
        argv = ['replay_evidence.py', 'reuse-check', 'M000001', str(out), '--checkout', str(self.project)]
        with patch.object(sys, 'argv', argv), patch.object(subprocess, 'run') as lake:
            with self.assertRaisesRegex(ValueError, 'Installed object mismatch'):
                evidence.main()
            installed.write_text('Fixture.Mod0')
            with patch.object(evidence, 'checkout_info', return_value=(
                    dict(**evidence.pins(), platform='x86_64-unknown-linux-gnu'), [], {})):
                with self.assertRaisesRegex(ValueError, 'platform/toolchain differ'):
                    evidence.main()
            lake.assert_not_called()

    @unittest.skipUnless(os.environ.get('REPLAY_NATIVE_TEST'), 'requires the pinned native Lean toolchain')
    def test_real_lake_twenty_assignments_and_restart(self):
        # A small independent Lean package exercises real native Lake, .olean
        # files, hashes, bundle generation and cache reuse without volunteer claims.
        elan_home = Path(os.environ.get('ELAN_HOME', Path.home() / '.elan')).resolve()
        (self.root / 'elan').symlink_to(elan_home, target_is_directory=True)
        (self.project / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
        (self.project / 'lakefile.toml').write_text('name = "fixture"\n[[lean_lib]]\nname = "Fixture"\nsrcDir = "src"\n')
        dep = self.project / '.lake/packages/mathlib'
        dep.mkdir(parents=True)
        subprocess.run(['git', 'init', '-q', dep], check=True)
        subprocess.run(['git', '-C', dep, '-c', 'user.name=Fixture', '-c', 'user.email=test@example.invalid',
                        'commit', '-qm', 'fixture', '--allow-empty'], check=True)
        self.summary['mathlib_commit'] = subprocess.check_output(['git', '-C', dep, 'rev-parse', 'HEAD'], text=True).strip()
        (self.tracker / 'summary.json').write_text(json.dumps(self.summary))
        # A cache hit must produce reviewable evidence even after restarting publication.
        self.assertEqual(tasks.run([self.rows[0]], self.project, self.root / 'prebuilt', False), 0)
        def build(target, number):
            out = self.root / str(number)
            if not (out / 'receipt.json').exists():
                self.build_count += 1
            self.assertEqual(worker_build.build(target, self.project, out), 0)
            return out
        self.gh.cut = 'build'
        with self.assertRaises(LostReply):
            self.launch(build)
        first = (self.root / '1/receipt.json').read_bytes()
        self.gh.cut = None
        self.assertEqual(self.launch(build), 0)
        self.assertEqual((len(self.gh.issues), self.build_count, len(set(self.gh.posts)), len(self.gh.posts)),
                         (20, 20, 20, 20))
        self.assertEqual((self.root / '1/receipt.json').read_bytes(), first)
        cached = self.root / '1'
        self.assertEqual(evidence.missing_targets(cached, [self.rows[0]]), [self.rows[0]])
        replay = json.loads((cached / evidence.REPLAY_FILE).read_text())
        self.assertEqual(replay['receipt_sha256'], tasks.digest(cached / 'receipt.json'))
        self.assertIn('replaying Fixture.Mod0', replay['transcript'].splitlines())
        comment = self.gh.history[1][-1]['body']
        self.assertIn(evidence.REPLAY_FILE, comment)
        self.assertIn('Lake built 0 and the kernel replayed 1 from cache', comment)
        self.assertFalse((self.root / '2' / evidence.REPLAY_FILE).exists())
        self.assertEqual(len(evidence.inventory(self.project, self.rows)['modules']), 20)
        # Reuse the whole packet, exercising actual independent checker
        # processes and the portable, per-command parallel receipt format.
        packet = self.root / 'parallel-packet'
        with patch.dict(os.environ, {'REPLAY_KERNEL_JOBS': '4'}):
            self.assertEqual(worker_build.build('P0001', self.project, packet), 0)
        parallel = json.loads((packet / evidence.REPLAY_FILE).read_text())
        self.assertEqual(len(parallel['replays']), 4)
        result = evidence.verify(packet, self.rows, {r['module']: r for r in self.rows}, self.project)
        self.assertEqual(result['kernel_replayed_targets'], [r['module'] for r in self.rows])
        argv = ['replay_evidence.py', 'reuse-check', 'M000001', str(self.root / '1'), '--checkout', str(self.project)]
        output = io.StringIO()
        with patch.object(sys, 'argv', argv), contextlib.redirect_stdout(output):
            evidence.main()
        self.assertEqual(json.loads(output.getvalue())['reuse_checked'], ['M000001'])

        # A receiver must reuse only the bundled outputs and compile a new
        # dependent module without the producer's generated setup inputs.
        self.assertTrue((self.project / '.lake/build/ir/Fixture/Mod0.setup.json').is_file())
        receiver = self.root / 'receiver'
        receiver.mkdir()
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(self.project / name, receiver / name)
        shutil.copytree(self.project / 'src', receiver / 'src')
        packages = receiver / '.lake/packages'
        packages.mkdir(parents=True)
        (packages / 'mathlib').symlink_to(dep, target_is_directory=True)
        for number in range(1, 21):
            with tarfile.open(self.root / str(number) / 'targets.tar.gz') as archive:
                self.assertFalse(any(m.name.endswith('.setup.json') for m in archive))
                archive.extractall(receiver / '.lake/build', filter='data')
        _, launcher, env = evidence.checkout_info(receiver)
        result = subprocess.run([*launcher, 'lake', '--no-build', '--no-cache', 'build',
                                 *['+' + r['module'] + ':olean' for r in self.rows]],
                                cwd=receiver, env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('All targets up-to-date', result.stdout + result.stderr)
        (receiver / 'src/Fixture/AfterTransfer.lean').write_text(
            'import Fixture.Mod0\nimport Fixture.Mod19\n'
            'theorem afterTransfer : True := fixture0\n')
        result = subprocess.run([*launcher, 'lake', '--no-cache', 'build',
                                 '+Fixture.AfterTransfer:olean'], cwd=receiver,
                                env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(tasks.rebuilt_imports(result.stdout + result.stderr,
                                             {r['module'] for r in self.rows}, set()), [])
        self.assertTrue((receiver / '.lake/build/lib/lean/Fixture/AfterTransfer.olean').is_file())
        self.assertEqual([p.name for p in (receiver / '.lake/build').rglob('*.setup.json')],
                         ['AfterTransfer.setup.json'])


if __name__ == '__main__':
    unittest.main()
