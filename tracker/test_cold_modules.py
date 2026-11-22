import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from contextlib import redirect_stdout
from unittest.mock import patch

import tasks


def row(task, packet, imports=(), state='open'):
    return dict(id=task, packet=packet, module=task, imports=imports,
                depth=int(bool(imports)), state=state)


class ClaimCommandTests(unittest.TestCase):
    def test_module_names_and_ids_use_canonical_claim_titles(self):
        first = dict(row('M000001', 'P0001'), module='Examples.First')
        second = dict(row('M000002', 'P0001'), module='Examples.Second')
        for target, claim_id in [('Examples.First', 'M000001'), ('M000001', 'M000001'),
                                 ('P0001', 'P0001')]:
            with self.subTest(target=target), patch.object(tasks, 'load', return_value=[first, second]), \
                 patch.object(tasks, 'claims', return_value=set()), \
                 patch.object(tasks, 'tracker_status', return_value='ok'), \
                 patch('sys.argv', ['tasks.py', 'claim', target]), \
                 patch.object(tasks.subprocess, 'run') as create:
                self.assertEqual(tasks.main(), 0)
                command = create.call_args.args[0]
                self.assertEqual(command[command.index('--title') + 1], 'Claim ' + claim_id)

    def test_stale_or_unverified_tracker_creates_no_claim(self):
        for status, message in [('stale', tasks.STALE_INDEX), ('unknown', tasks.UNVERIFIED_INDEX)]:
            with self.subTest(status=status), patch.object(tasks, 'load', return_value=[row('M000001', 'P0001')]), \
                 patch.object(tasks, 'claims', return_value=set()), \
                 patch.object(tasks, 'tracker_status', return_value=status), \
                 patch('sys.argv', ['tasks.py', 'claim', 'M000001']), \
                 patch.object(tasks.subprocess, 'run') as create:
                with self.assertRaises(SystemExit) as stopped:
                    tasks.main()
                self.assertEqual(str(stopped.exception), message)
                create.assert_not_called()


class TrackerStatusTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.base = Path(tmp.name)
        for name in tasks.TRACKED:
            (self.base / name).write_text(name)
        change = patch.object(tasks, 'base', self.base)
        change.start()
        self.addCleanup(change.stop)

    def status(self, remote, hashed=('a1', 'b2'), hash_error=None):
        hashes = iter(hashed)

        def hash_object(command, **kwargs):
            self.assertEqual(command[:4], ['git', '-C', str(self.base), 'hash-object'])
            self.assertNotIn('--no-filters', command)
            if hash_error:
                raise hash_error
            return subprocess.CompletedProcess(command, 0, next(hashes) + '\n', '')

        def graphql(command, **kwargs):
            if isinstance(remote, Exception):
                raise remote
            return json.dumps({'data': {'repository': remote}})

        with patch.object(tasks.subprocess, 'run', side_effect=hash_object), \
             patch.object(tasks.subprocess, 'check_output', side_effect=graphql):
            return tasks.tracker_status()

    def test_matching_blobs_are_ok(self):
        self.assertEqual(self.status({'f0': {'oid': 'a1'}, 'f1': {'oid': 'b2'}}), 'ok')

    def test_a_differing_blob_is_stale(self):
        self.assertEqual(self.status({'f0': {'oid': 'a1'}, 'f1': {'oid': 'c3'}}), 'stale')

    def test_a_file_missing_on_main_is_stale(self):
        self.assertEqual(self.status({'f0': {'oid': 'a1'}, 'f1': None}), 'stale')

    def test_a_file_absent_on_both_sides_matches(self):
        (self.base / 'completed.tsv').unlink()
        self.assertEqual(self.status({'f0': {'oid': 'a1'}, 'f1': None}, hashed=('a1',)), 'ok')

    def test_git_failure_is_stale(self):
        self.assertEqual(self.status({'f0': {'oid': 'a1'}, 'f1': {'oid': 'b2'}},
                                     hash_error=subprocess.CalledProcessError(128, 'git')), 'stale')

    def test_github_failure_is_unknown(self):
        for failure in (subprocess.CalledProcessError(1, 'gh'), OSError('no gh')):
            with self.subTest(failure=type(failure).__name__):
                self.assertEqual(self.status(failure), 'unknown')
        self.assertEqual(self.status({}), 'unknown')


class OpenIssueTests(unittest.TestCase):
    def test_saved_active_credential_uses_authenticated_pagination(self):
        with patch.object(tasks, 'which', return_value='/bin/gh'), \
             patch.object(tasks.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0)) as auth, \
             patch.object(tasks.subprocess, 'check_output', return_value='[{"number": 1}][{"number": 2}]') as api, \
             patch.object(tasks.urllib.request, 'urlopen') as anonymous:
            self.assertEqual(list(tasks.open_issues()), [{'number': 1}, {'number': 2}])

        auth.assert_called_once_with(
            ['/bin/gh', 'auth', 'token', '--hostname', 'github.com'],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
        api.assert_called_once_with(
            ['/bin/gh', 'api', '--hostname', 'github.com', '--paginate',
             f'repos/{tasks.repo}/issues?state=open&per_page=100'], text=True,
        )
        anonymous.assert_not_called()


class ClaimLookupTests(unittest.TestCase):
    def test_authenticated_lookup_reads_unlabeled_claims_across_pages(self):
        pages = [
            {'data': {'repository': {'issues': {'nodes': [{'title': title} for title in titles]}}}}
            for titles in [['Claim M000001', 'Claim M000002 edited'], ['Claim P0123', 'Other issue']]
        ]
        with patch.object(tasks, 'authenticated_gh', return_value='/bin/gh'), \
             patch.object(tasks.subprocess, 'check_output', return_value=json.dumps(pages)) as api, \
             patch.object(tasks, 'open_issues') as rest:
            self.assertEqual(tasks.claims(), {'M000001', 'P0123'})

        command = api.call_args.args[0]
        self.assertEqual(command[:7],
                         ['/bin/gh', 'api', 'graphql', '--hostname', 'github.com', '--paginate', '--slurp'])
        self.assertIn('nodes { title }', command[-1])
        rest.assert_not_called()

    def test_anonymous_lookup_filters_pull_request_titles(self):
        issues = [{'title': 'Claim M000001'},
                  {'title': 'Claim M000002', 'pull_request': {}},
                  {'title': 'Claim P0123'}]
        with patch.object(tasks, 'which', return_value=None), \
             patch.object(tasks.json, 'load', return_value=issues), \
             patch.object(tasks.urllib.request, 'urlopen') as fetch, \
             patch.object(tasks.subprocess, 'check_output') as cli:
            fetch.return_value.__enter__.return_value.headers = {}
            self.assertEqual(tasks.claims(), {'M000001', 'P0123'})

        request = fetch.call_args.args[0]
        self.assertEqual(request.full_url,
                         f'https://api.github.com/repos/{tasks.repo}/issues?state=open&per_page=100')
        cli.assert_not_called()


class ColdModuleTests(unittest.TestCase):
    def test_claims_and_ledger_states(self):
        rows = [row('M1', 'P1'), row('M2', 'P1'), row('M3', 'P2'),
                row('M4', 'P3', state='build-observed'), row('M5', 'P3', state='assigned')]
        self.assertEqual([r['id'] for r, _, _ in tasks.cold_modules(rows, {'M1', 'P2'})], ['M2'])
        self.assertEqual(tasks.cold_modules(rows, {'P1', 'P2'}), [])

    def test_rank_by_sole_import_then_direct_consumers_then_id(self):
        rows = [row('A', 'P1'), row('B', 'P1'), row('C', 'P1'), row('D', 'P1'),
                row('E', 'P2', ['A', 'A']), row('F', 'P2', ['B', 'C']),
                row('G', 'P2', ['B', 'C']), row('H', 'P3', ['D']),
                row('I', 'P4', ['D']), row('J', 'P5', ['D'], state='assigned')]
        ranked = tasks.cold_modules(rows, {'P3', 'I'})
        self.assertEqual([(r['id'], sole, direct) for r, sole, direct in ranked],
                         [('A', 1, 1), ('B', 0, 2), ('C', 0, 2), ('D', 0, 0)])

    def test_cold_cli_and_default_packet_suggestions(self):
        rows = [row('M1', 'P1'), row('M2', 'P1', state='assigned'), row('M3', 'P2', ['M1'])]
        def next_output(*args):
            output = io.StringIO()
            with patch.object(tasks, 'load', return_value=rows), patch.object(tasks, 'claims', return_value=set()), \
                 patch('sys.argv', ['tasks.py', 'next', *args]), redirect_stdout(output):
                self.assertEqual(tasks.main(), 0)
            return output.getvalue()
        self.assertEqual(next_output(), 'P2 depth 1 begins with M3 1/1 open\n')
        self.assertEqual(next_output('--cold', '--limit', '1'),
                         'M1 P1 M1 sole-project-import consumers 1 direct consumers 1\n')
        self.assertEqual(next_output('--cold', '--limit', '0'), '')


def prow(task, packet, depth=0, state='open'):
    return dict(id=task, packet=packet, module=task, imports=[],
                depth=depth, state=state)


class PacketSuggestionTests(unittest.TestCase):
    def setUp(self):
        self.rows = [
            prow('M1', 'P1'), prow('M2', 'P1'),
            prow('M3', 'P2', state='build-observed'), prow('M4', 'P2'),
            prow('M5', 'P3', state='wave-reused'), prow('M6', 'P3', state='assigned'),
            prow('M7', 'P4', state='volunteer-build-reviewed'),
            prow('M8', 'P5', depth=1, state='pilot-reused'), prow('M9', 'P5', depth=1),
            prow('M10', 'P5', depth=1),
            prow('M11', 'P6', depth=1, state='build-observed'), prow('M12', 'P6', depth=1),
        ]

    def test_default_lists_only_fully_open_packets(self):
        full, partial = tasks.packet_suggestions(self.rows, set())
        self.assertEqual([(r['packet'], o, t) for r, o, t in full], [('P1', 2, 2)])
        self.assertEqual(partial, [])

    def test_partial_packets_need_open_modules_and_no_assigned(self):
        full, partial = tasks.packet_suggestions(self.rows, set(), include_partial=True)
        self.assertEqual([(r['packet'], o, t) for r, o, t in partial],
                         [('P2', 1, 2), ('P5', 2, 3), ('P6', 1, 2)])

    def test_claimed_packet_or_module_hides_the_packet(self):
        for busy in ({'P2'}, {'M4'}, {'P1'}):
            full, partial = tasks.packet_suggestions(self.rows, busy, include_partial=True)
            shown = [r['packet'] for r, _, _ in full + partial]
            if 'P1' in busy:
                self.assertNotIn('P1', shown)
            else:
                self.assertNotIn('P2', shown)

    def test_partial_cli_output(self):
        def next_output(*args):
            output = io.StringIO()
            with patch.object(tasks, 'load', return_value=self.rows), \
                 patch.object(tasks, 'claims', return_value=set()), \
                 patch('sys.argv', ['tasks.py', 'next', *args]), redirect_stdout(output):
                self.assertEqual(tasks.main(), 0)
            return output.getvalue()
        self.assertEqual(next_output(),
                         'P1 depth 0 begins with M1 2/2 open\n')
        self.assertEqual(next_output('--include-partial'),
                         'P1 depth 0 begins with M1 2/2 open\n'
                         'P2 depth 0 begins with M4 1/2 open (partial)\n'
                         'P5 depth 1 begins with M9 2/3 open (partial)\n'
                         'P6 depth 1 begins with M12 1/2 open (partial)\n'
                         'Partial packets already have evidence for some modules and cannot be claimed as a packet.\n'
                         'Claim their open modules individually: show <packet> lists them, then claim <module ID>.\n')


if __name__ == '__main__':
    unittest.main()
