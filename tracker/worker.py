"""Dispatch granted replay tasks to one isolated Docker worker and publish verified evidence."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import fcntl
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile
import time
import uuid

import replay_evidence as evidence
import tasks
from worker_github import GitHub

FILES = ('receipt.json', 'build.log', 'targets.tar.gz')
OCCUPIED = 'Selection is occupied in the ledger or live claims'
CONFLICT = 'closed or conflicting claim'
# Another reservation winning the same work is expected and leaves nothing to repair.
LOST_RACES = (OCCUPIED, CONFLICT)


def save(path, state):
    tmp = path.with_suffix('.tmp')
    tmp.write_text(json.dumps(state, indent=2) + '\n')
    tmp.replace(path)


def plan(assignments, rows):
    ids = assignments.read_text().split()
    if not ids or any(not re.fullmatch(r'M\d{6}|P\d{4}', i) for i in ids):
        raise ValueError('Expected a list of module or packet IDs')
    wanted = set(ids)
    selected = {i: [] for i in ids}
    for row in rows:
        for i in wanted.intersection((row['id'], row['packet'])):
            selected[i].append(row)
    all_ids = [r['id'] for i in ids for r in selected[i]]
    if not all(selected.values()) or len(all_ids) != len(set(all_ids)):
        raise ValueError('Unknown or overlapping assignments')
    return selected


class DockerBuilder:
    def __init__(self, args, directory, selected):
        self.selected = selected
        self.container = args.container
        self.tracker = PurePosixPath(args.container_repo) / 'tracker/worker_build.py'
        self.checkout = args.checkout
        self.root = PurePosixPath(args.receipts)
        self.directory = directory
        self.retry = set(args.retry)

    def preflight(self):
        cmd = ['docker', 'exec', self.container, 'python3', str(self.tracker), 'identity', self.checkout]
        identity = json.loads(subprocess.check_output(cmd, text=True))
        evidence.require(all(identity.get(k) == v for k, v in evidence.pins().items()),
                         'Builder pins differ from controller')
        return identity

    def __call__(self, target, number):
        remote = self.root / f'{target}-{number}'
        local = self.directory / str(number)
        if local.exists() and ((local / evidence.REPLAY_FILE).is_file()
                               or not evidence.missing_targets(local, self.selected[target])):
            return local
        command = ['docker', 'exec', self.container, 'python3', str(self.tracker),
                   'build', target, self.checkout, str(remote)]
        if target in self.retry:
            command.append('--retry-failed')
        with (self.directory / f'{number}.log').open('a') as log:
            subprocess.run(command, check=True, stdout=log, stderr=subprocess.STDOUT)
        with tempfile.TemporaryDirectory(dir=self.directory) as tmp:
            stage = Path(tmp) / 'artifacts'
            stage.mkdir()
            def fetch(name):
                dest = stage / name
                subprocess.run(['docker', 'cp', f'{self.container}:{remote}/{name}', str(dest)], check=True)
                evidence.require(dest.is_file() and not dest.is_symlink(), 'Unexpected artifact: ' + name)

            if local.exists():
                # Upgrade a pre-existing controller mirror after the builder has replayed its targets.
                fetch(evidence.REPLAY_FILE)
                (stage / evidence.REPLAY_FILE).replace(local / evidence.REPLAY_FILE)
            else:
                for name in FILES:
                    fetch(name)
                if evidence.missing_targets(stage, self.selected[target]):
                    fetch(evidence.REPLAY_FILE)
                stage.rename(local)
        return local


def inspect_grant(issue, comments, target, owner):
    if ('pull_request' in issue or issue['title'] != 'Claim ' + target
            or issue['user']['login'].casefold() != owner.casefold()):
        return 'wrong claim', None
    for c in comments:
        lines = c['body'].splitlines()
        if c['user']['login'].casefold() == owner.casefold() and lines and lines[0].strip().casefold() == 'replay submission':
            return 'submitted', c['html_url']
    labels = {label['name'] for label in issue['labels']}
    if issue['state'] != 'open' or 'claim-conflict' in labels:
        return CONFLICT, None
    if 'claim-granted' in labels and any(c['user']['login'] == 'github-actions[bot]'
            and c['body'].startswith(f'Granted `{target}`.') for c in comments):
        return 'granted', None
    return 'pending', None


def dispatch(state, selected, rows, github, build, persist, jobs, poll, retry):
    entries = state['tasks']
    running = {}
    # Set once main's tracker files differ from this checkout's. This process never pulls, so it
    # stays set: no new claims, but outstanding grants still build and submit, then the run exits 1.
    # Unclaimed entries keep no error, so a restart after pulling resumes them without --retry.
    block_admits = False
    # Only Docker work runs concurrently. One coordinator owns claim creation,
    # the journal, grant decisions and publication.
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while True:
            unverified = False
            pending = [t for t, e in entries.items() if not (e.get('submission') or e.get('error'))]
            if not pending:
                return int(any(e.get('error') and e['error'] not in LOST_RACES for e in entries.values()))
            # A failed build can still hold an open grant. It consumes capacity
            # until the operator retries it or the issue is closed.
            failed = [e for e in entries.values() if e.get('error')]
            held = sum(1 for e in failed if not e.get('issue') and e.get('intent') == 'claim')
            for issue in github.watch([e['issue'] for e in failed if e.get('issue')]):
                if issue['state'] == 'open' and 'claim-conflict' not in {l['name'] for l in issue['labels']}:
                    held += 1
            outstanding = sum(bool(entries[t].get('issue') or entries[t].get('intent')) for t in pending)
            if not outstanding and held >= jobs:
                print('Failed reservations occupy all slots. Inspect the journal before resuming.', file=sys.stderr)
                return 1
            active = outstanding + held
            can_admit = not block_admits and active < jobs and any(not entries[t].get('issue') for t in pending)
            watch = [entries[t]['issue'] for t in pending if entries[t].get('issue')
                     and (t not in running or running[t].done())]
            retrying_claim = any(t in retry and entries[t].get('intent') == 'claim' for t in pending)
            snapshot = github.snapshot() if can_admit or retrying_claim else github.watch(watch)
            open_issues = {i['number']: i for i in snapshot if 'pull_request' not in i}
            busy = {i['title'][6:] for i in open_issues.values() if i['title'].startswith('Claim ')}
            for target in pending:
                entry = entries[target]
                marker = f"<!-- replay-worker {state['id']} {target} -->"
                number = entry.get('issue')
                if not number:
                    if entry.get('intent') == 'claim':
                        existing = github.find_claim(marker)
                        if existing:
                            number = existing['number']
                        elif target not in retry:
                            entry['error'] = 'Unconfirmed claim creation. Check GitHub before using --retry.'
                    elif block_admits or active >= jobs:
                        continue
                    else:
                        active += 1
                    if not number and not entry.get('error'):
                        if any(r['state'] != 'open' or r['id'] in busy or r['packet'] in busy for r in selected[target]):
                            entry['error'] = OCCUPIED
                        elif (fresh := github.fresh()) != 'ok':
                            # Nothing is journaled: the entry stays unclaimed and error-free.
                            if fresh == 'stale':
                                block_admits = True
                                print(tasks.STALE_INDEX, 'Finishing outstanding grants without new claims.',
                                      file=sys.stderr)
                            else:
                                unverified = True
                            continue
                        else:
                            entry['intent'] = 'claim'
                            persist()
                            number = github.claim(target, marker)['number']
                    if number:
                        entry.update(issue=number, intent=None)
                    persist()
                    if not number:
                        continue
                future = running.get(target)
                if future and not future.done():
                    continue
                issue = open_issues.get(number) or github.issue(number)
                comments = github.comments(number) if issue['comments'] else []
                status, url = inspect_grant(issue, comments, target, github.owner)
                if url:
                    entry.update(submission=url, intent=None)
                elif status == 'pending':
                    if future:
                        del running[target]
                    continue
                elif status != 'granted':
                    # The bot asks claimants to close a conflicting request. Close before
                    # journaling the error, because a restart skips errored entries.
                    if status == CONFLICT and issue['state'] == 'open':
                        github.close(number)
                    entry['error'] = status
                elif not future:
                    if len(running) >= jobs:
                        continue
                    running[target] = pool.submit(build, target, number)
                    continue
                else:
                    del running[target]
                    try:
                        local = future.result()
                        result = evidence.verify(local, selected[target], rows)
                        files = [local / name for name in FILES]
                        if result['kernel_replayed_targets']:
                            files.append(local / evidence.REPLAY_FILE)
                        links = github.publish_assets(number, target, files)
                    except (ValueError, OSError, KeyError, subprocess.CalledProcessError) as exc:
                        entry['error'] = str(exc)
                        persist()
                        continue
                    # Release upload may take time. Check authority and existing
                    # comments again immediately before the only submission write.
                    status, url = inspect_grant(github.issue(number), github.comments(number), target, github.owner)
                    if url:
                        entry.update(submission=url, intent=None)
                    elif status != 'granted':
                        entry['error'] = 'Grant changed before publication: ' + status
                    elif entry.get('intent') == 'submit' and target not in retry:
                        entry['error'] = 'Unconfirmed submission. Check GitHub before using --retry.'
                    else:
                        receipt = json.loads(files[0].read_text())
                        body = (f"Replay submission\n\n{target}, Lake exit 0 on {result['identity']['platform']}. "
                                f"Of {len(result['tasks'])} requested targets, Lake built "
                                f"{len(result['built_targets'])} and the kernel replayed "
                                f"{len(result['kernel_replayed_targets'])} from cache. "
                                f"Elapsed Lake time {receipt['elapsed_seconds']} s.\n\n"
                                f"{links}\n\nBundle SHA-256 `{receipt['bundle_sha256']}`.\n\n{marker}")
                        entry['intent'] = 'submit'
                        persist()
                        entry.update(submission=github.submit(number, body), intent=None)
                if entry.get('error') or entry.get('submission'):
                    running.pop(target, None)
                    print(target, entry.get('error') or entry['submission'], flush=True)
                persist()
            if any(not (e.get('submission') or e.get('error')) for e in entries.values()):
                remaining = [e for e in entries.values() if not (e.get('error') or e.get('submission'))]
                in_flight = sum(bool(e.get('issue') or e.get('intent')) for e in remaining)
                if block_admits and not in_flight and not running:
                    print('Claims stopped because the tracker checkout is behind main. Pull on the controller '
                          'and the builder, then restart with the same command.', file=sys.stderr)
                    return 1
                if (not block_admits and not unverified
                        and any(not e.get('issue') and not e.get('intent') for e in remaining)
                        and in_flight + held < jobs):
                    continue
                futures = list(running.values())
                if futures:
                    wait(futures, timeout=poll, return_when=FIRST_COMPLETED)
                else:
                    time.sleep(poll)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('assignments', type=Path)
    parser.add_argument('state_dir', type=Path)
    parser.add_argument('--fork', required=True, help='OWNER/REPO for evidence releases')
    parser.add_argument('--container', required=True)
    parser.add_argument('--container-repo', default='/work/repo')
    parser.add_argument('--checkout', default='/work/vol/lean')
    parser.add_argument('--receipts', default='/work/receipts')
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--poll', type=int, default=20, help='maximum seconds between grant checks')
    parser.add_argument('--retry', action='append', default=[], metavar='ID',
                        help='retry a failed assignment after inspecting its recorded error')
    args = parser.parse_args()
    if min(args.jobs, args.poll) < 1:
        parser.error('--jobs and --poll must be positive')
    directory = args.state_dir.resolve()
    directory.mkdir(parents=True, exist_ok=True)
    with (directory / 'worker.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        github = GitHub(args.fork)
        rows = {r['module']: r for r in tasks.load()}
        selected = plan(args.assignments, rows.values())
        builder = DockerBuilder(args, directory, selected)
        config = dict(owner=github.owner, fork=github.fork, container=args.container,
                      checkout=args.checkout, receipts=args.receipts, container_repo=args.container_repo,
                      assignments=list(selected), builder=builder.preflight())
        journal = directory / 'state.json'
        state = (json.loads(journal.read_text()) if journal.exists() else
                 dict(config=config, id=uuid.uuid4().hex, tasks={t: {} for t in selected}))
        evidence.require(state['config'] == config, 'State belongs to a different worker or assignment list')
        for t in args.retry:
            evidence.require(t in selected, 'Unknown retry target: ' + t)
            state['tasks'][t].pop('error', None)
        save(journal, state)
        return dispatch(state, selected, rows, github, builder,
                        lambda: save(journal, state), args.jobs, args.poll, set(args.retry))


if __name__ == '__main__':
    sys.exit(main())
