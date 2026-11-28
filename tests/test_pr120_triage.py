"""Offline regression tests for PR #120 claim preflight."""

from contextlib import redirect_stdout, redirect_stderr
import importlib.util
import io
import json
import locale
import os
import sys
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "pr120-triage.py"
SPEC = importlib.util.spec_from_file_location("pr120_triage", SCRIPT)
triage = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(triage)


def report(head="abcdef1", rows=None):
    if rows is None:
        rows = ["| `Development/Foo.lean:12` | instance | timeout | |"]
    return (f"Branch `owner/repo:branch`, head `{head}`.\n\n## Open ({len(rows)})\n\n"
            "| Module (file:line) | Category | First error | Notes |\n|---|---|---|---|\n"
            + "\n".join(rows) + "\n\n## Changed since this error (likely fixed, rebuilding)\n"
            "| `Development/AlreadyFixed.lean:1` | other | old error | |\n")


class ReportTests(unittest.TestCase):
    def test_unicode_claim_and_changed_section(self):
        head, rows = triage.parse_report(report(rows=[
            "| `Development/GaloisCohomology₂/Foo.lean:123` | other | error | claimed: #18 @owner |",
        ]))
        self.assertEqual(head, "abcdef1")
        self.assertEqual(rows, [{"path": "src/Development/GaloisCohomology₂/Foo.lean",
                                 "line": 123, "reported_claims": [18]}])

    def test_zero_open_failures(self):
        self.assertEqual(triage.parse_report(report(rows=[]))[1], [])

    def test_lookahead_rows_are_not_attributed_to_normal_build_head(self):
        text = report() + ("\n## Look-ahead: all known errors (preview)\n"
                           "| `Development/Hidden.lean:10` | 7 | error | timeout |\n")
        self.assertEqual(len(triage.parse_report(text)[1]), 1)

    def test_unrecognized_format_fails_instead_of_hiding_rows(self):
        for text in [report().replace("## Open (1)", "## Failures (1)"),
                     report().replace("Foo.lean:12", "Foo.lean (12)"),
                     report().replace("head `abcdef1`", "head unavailable")]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                triage.parse_report(text)

    def test_parent_path_is_rejected(self):
        with self.assertRaises(ValueError):
            triage.parse_report(report(rows=["| `../Foo.lean:1` | other | error | | "]))


class ClaimTests(unittest.TestCase):
    def test_empty_draft_reserves_only_the_full_dotted_module_title(self):
        _, failures = triage.parse_report(report(rows=[
            "| `Development/GaloisCohomology₂/Foo.lean:1` | other | error | |",
            "| `Development/Other/Foo.lean:2` | other | error | |",
        ]))
        pr = {"number": 1065, "url": "url", "title": "Fix Development.GaloisCohomology₂.Foo",
              "changedFiles": 0, "files": []}
        with patch.object(triage, "run", return_value=json.dumps([pr])) as run:
            claims, incomplete, truncated = triage.fetch_claims(failures)
        self.assertIn("title", run.call_args.args[0][-1].split(","))
        self.assertFalse(incomplete or truncated)
        rows = triage.triage(failures, {row["path"] for row in failures}, set(), set(), claims, True)
        self.assertEqual([row["claim_status"] for row in rows], ["claimed", "unclaimed"])

    def test_titles_do_not_override_nonempty_diffs_or_match_partial_names(self):
        _, failures = triage.parse_report(report())
        for title, files in [
            ("Fix Foo", []),
            ("Fix Development.Foo and Development.Bar", []),
            ("Fix Development.Foo", [{"path": "src/Other.lean"}]),
        ]:
            with self.subTest(title=title, files=files):
                claims, _, _ = triage.index_claims([
                    {"number": 1, "url": "url", "title": title,
                     "changedFiles": len(files), "files": files}], failures)
                self.assertNotIn("src/Development/Foo.lean", claims)

    def test_large_pr_files_are_paginated_before_declaring_unclaimed(self):
        pr = {"number": 18, "url": "url", "changedFiles": 2,
              "files": [{"path": "src/First.lean"}]}
        pages = [[{"filename": "src/First.lean"}], [{"filename": "src/Development/Foo.lean"}]]
        with patch.object(triage, "run", side_effect=[json.dumps([pr]), json.dumps(pages)]) as run:
            claims, incomplete, truncated = triage.fetch_claims()
        self.assertEqual(claims["src/Development/Foo.lean"][0]["number"], 18)
        self.assertFalse(incomplete or truncated)
        self.assertIn("--paginate", run.call_args_list[1].args[0])

    def test_multiple_live_prs_reserve_same_module(self):
        prs = [{"number": n, "url": f"https://github.com/o/r/pull/{n}",
                "changedFiles": 1, "files": [{"path": "src/Development/Foo.lean"}]}
               for n in [10, 11]]
        claims, incomplete, truncated = triage.index_claims(prs)
        rows = triage.triage(triage.parse_report(report())[1], {"src/Development/Foo.lean"},
                             set(), set(), claims, True)
        self.assertFalse(incomplete or truncated)
        self.assertEqual(rows[0]["claim_status"], "claimed")
        self.assertEqual([p["number"] for p in rows[0]["live_claims"]], [10, 11])

    def test_truncated_file_list_never_implies_unclaimed(self):
        prs = [{"number": 15, "url": "url", "changedFiles": 200,
                "files": [{"path": "src/SomeOtherFile.lean"}]}]
        claims, incomplete, truncated = triage.index_claims(prs)
        self.assertEqual(incomplete, [15])
        rows = triage.triage(triage.parse_report(report())[1], {"src/Development/Foo.lean"},
                             set(), set(), claims, not incomplete and not truncated)
        self.assertEqual(rows[0]["claim_status"], "unknown")

    def test_reported_claim_is_retained_when_live_diff_is_empty(self):
        _, failures = triage.parse_report(report(rows=[
            "| `Development/Foo.lean:12` | other | error | claimed: #18 @owner |",
        ]))
        rows = triage.triage(failures, {failures[0]["path"]}, set(), set(), {}, True)
        self.assertEqual(rows[0]["claim_status"], "reported claim")


class CheckoutTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Test")
        self.git("config", "user.email", "test@example.invalid")
        self.write("src/Development/Foo.lean", "-- original\n")
        self.write("src/Development/Stable.lean", "-- stable\n")
        self.write("src/Development/GaloisCohomology₂/Deleted.lean", "-- deleted\n")
        self.commit()
        self.base = self.git("rev-parse", "HEAD").strip()

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.root), *args], text=True, encoding="utf-8")

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text, encoding="utf-8")

    def commit(self):
        self.git("add", ".")
        self.git("commit", "-qm", "test snapshot")

    def test_committed_local_and_deleted_files_are_distinct(self):
        self.write("src/Development/Foo.lean", "-- changed\n")
        (self.root / "src/Development/GaloisCohomology₂/Deleted.lean").unlink()
        self.commit()
        self.write("src/Development/Stable.lean", "-- unstaged\n")
        self.write("src/Development/New.lean", "-- untracked\n")
        before = self.git("status", "--porcelain")
        _, tracked, local, changed, warning = triage.inspect_checkout(self.root, self.base[:10])
        self.assertIsNone(warning)
        self.assertEqual(changed, {"src/Development/Foo.lean", "src/Development/GaloisCohomology₂/Deleted.lean"})
        self.assertEqual(local, {"src/Development/Stable.lean", "src/Development/New.lean"})
        self.assertNotIn("src/Development/GaloisCohomology₂/Deleted.lean", tracked)
        self.assertEqual(before, self.git("status", "--porcelain"))

    def test_sparse_checkout_is_not_mistaken_for_deleted_source(self):
        self.git("sparse-checkout", "set", "--no-cone", "/src/Development/Foo.lean")
        _, tracked, local, changed, _ = triage.inspect_checkout(self.root, self.base)
        self.assertIn("src/Development/Stable.lean", tracked)
        self.assertFalse(local or changed)

    def test_staged_rename_marks_both_paths_as_locally_edited(self):
        old = "src/Development/Foo.lean"
        new = "src/Development/New.lean"
        self.git("config", "diff.renames", "true")
        self.git("mv", old, new)
        _, tracked, local, changed, _ = triage.inspect_checkout(self.root, self.base)
        self.assertEqual(local, {old, new})
        rows = triage.triage(triage.parse_report(report(self.base))[1], tracked, local, changed, {}, False)
        self.assertEqual(rows[0]["source"], "local edits")

    def test_committed_rename_reports_old_and_new_paths(self):
        self.git("config", "diff.renames", "true")
        self.git("mv", "src/Development/Foo.lean", "src/Development/New.lean")
        self.commit()
        _, _, local, changed, _ = triage.inspect_checkout(self.root, self.base)
        self.assertFalse(local)
        self.assertEqual(changed, {"src/Development/Foo.lean", "src/Development/New.lean"})

    def test_unicode_subprocess_output_ignores_default_decoder(self):
        data = "src/Development/GaloisCohomology₂/Foo.lean\0"
        code = f"import sys; sys.stdout.buffer.write({data.encode('utf-8')!r})"
        decoder = "getencoding" if hasattr(locale, "getencoding") else "getpreferredencoding"
        with patch.object(locale, decoder, return_value="cp1252"):
            decoded = triage.run([sys.executable, "-c", code])
        self.assertEqual(triage.nul_paths(decoded), {data.rstrip("\0")})

    def test_cli_reads_and_writes_utf8_with_legacy_io_defaults(self):
        module = "src/Development/GaloisCohomology₂/Foo.lean"
        self.write(module, "-- Unicode path\n")
        self.commit()
        head = self.git("rev-parse", "HEAD").strip()
        report_path = self.root / "report.md"
        report_path.write_text(report(head, [
            f"| `{module[4:]}:1` | other | curly quote \u201d | |",
        ]), encoding="utf-8")
        env = dict(os.environ, PYTHONUTF8="0", PYTHONIOENCODING="cp1252")
        for flags in [[], ["--json"]]:
            with self.subTest(flags=flags):
                output = subprocess.check_output([
                    sys.executable, str(SCRIPT), "--checkout", str(self.root),
                    "--report", str(report_path), "--offline", *flags,
                ], env=env, encoding="utf-8")
                self.assertIn(module, output)
                if flags:
                    self.assertEqual(json.loads(output)["failures"][0]["path"], module)

    def test_missing_report_commit_is_unknown(self):
        _, _, _, changed, warning = triage.inspect_checkout(self.root, "1" * 40)
        self.assertIsNone(changed)
        self.assertIn("unavailable locally", warning)

    def test_older_checkout_is_not_treated_as_changes_since_report(self):
        self.write("src/Development/Foo.lean", "-- newer build source\n")
        self.commit()
        newer_build = self.git("rev-parse", "HEAD").strip()
        self.git("checkout", "--quiet", "--detach", self.base)
        _, _, _, changed, warning = triage.inspect_checkout(self.root, newer_build)
        self.assertIsNone(changed)
        self.assertIn("not a verified descendant", warning)

    def test_offline_json_cli_does_not_call_github(self):
        report_path = self.root / "report.md"
        report_path.write_text(report(self.base), encoding="utf-8")
        original_run = triage.run

        def local_only(args):
            self.assertEqual(args[0], "git")
            return original_run(args)

        output = io.StringIO()
        with patch.object(triage, "run", side_effect=local_only), redirect_stdout(output):
            code = triage.main(["--checkout", str(self.root), "--report", str(report_path), "--offline", "--json"])
        self.assertEqual(code, 0)
        data = json.loads(output.getvalue())
        self.assertEqual(data["failures"][0]["source"], "unchanged since report")
        self.assertEqual(data["failures"][0]["claim_status"], "unknown")
        self.assertTrue(data["warnings"])

    def test_github_failure_exits_nonzero(self):
        report_path = self.root / "report.md"
        report_path.write_text(report(self.base), encoding="utf-8")
        original_run = triage.run

        def fail_github(args):
            if args[0] == "gh":
                raise RuntimeError("GitHub is unavailable")
            return original_run(args)

        error = io.StringIO()
        with patch.object(triage, "run", side_effect=fail_github), redirect_stderr(error):
            code = triage.main(["--checkout", str(self.root), "--report", str(report_path)])
        self.assertEqual(code, 2)
        self.assertIn("GitHub is unavailable", error.getvalue())


if __name__ == "__main__":
    unittest.main()
