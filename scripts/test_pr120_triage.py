import json
import random
from pathlib import Path
import subprocess
import shutil
import sys
import tempfile
import unittest

from pr120_triage import count_impacts, header_imports, make_report, tracker_rows


MARKDOWN = r"""# PR #120 — open build failures
Branch `org/repo:topic`, head `abcd123401`. Updated 2026-11-24 03:06 UTC.
## Open (4)
| Module (file:line) | Category | First error | Notes |
|---|---|---|---|
| `src/A.lean:4` | instance | a pipe \| in the message | |
| `B.lean:9` | other | blah `foo` | claimed: #15 @alice |
| `Dir/C.lean:3:2` | ambiguous name | X | fix exists on branch |
| `Missing.lean:1` | other | missing root | |
## Changed since this error (likely fixed, rebuilding)
| `G.lean:78` | other | old | |
## Open PRs not auto-merged
| `Ignore.lean:1` | other | don't read | |
"""


class TriageTests(unittest.TestCase):
    def test_tracker_sections_statuses_and_head(self):
        rows, rev, date, warnings = tracker_rows(MARKDOWN)
        self.assertEqual(set(rows), {"A", "B", "Dir.C", "Missing", "G"})
        self.assertEqual(rev, "abcd123401")
        self.assertEqual(date, "2026-11-24 03:06 UTC")
        self.assertEqual(warnings, [])
        self.assertEqual([rows[x].tracker_status for x in ["A", "B", "Dir.C", "G"]],
                         ["open_unclaimed", "open_claimed", "open_fix_exists", "changed_rebuilding"])
        self.assertEqual(rows["Dir.C"].line, 3)
        self.assertFalse(rows["G"].active)
        self.assertTrue(tracker_rows(MARKDOWN.replace("Open (4)", "Open (5)"))[3])

    def test_lean_header_comments_and_modifiers(self):
        source = """\ufeff/-! Lean file /- nested import Bogus -/ -/
module
prelude
public import A.B -- import NotReal
public meta import
    /- inline -/ «A-text».C₂
import all D.E
-- import Nope
@[expose] public section
def s := "import AlsoNotReal"
"""
        self.assertEqual(list(header_imports(source)), ["A.B", "A-text.C₂", "D.E"])
        self.assertEqual(list(header_imports("import Mathlib\nopen X\nimport notHeader")), ["Mathlib"])

    def test_overlap_active_ancestor_and_cycle(self):
        reverse = {"A": ["B", "D"], "B": ["D", "E"], "D": ["F"], "E": [], "F": ["D"], "U": []}
        counts, union = count_impacts(reverse, ["A", "B", "missing"])
        self.assertEqual(counts, {"A": (4, 0), "B": (3, 0), "missing": (None, None)})
        self.assertEqual(union, 5)

    def test_impact_against_independent_search(self):
        rng = random.Random(120)
        nodes = list(map(str, range(14)))
        for run in range(250):
            graph = {a: [b for b in nodes if rng.random() < (run % 5) / 20] for a in nodes}
            roots = rng.sample(nodes, rng.randint(1, 6))
            reached = {}
            for root in roots:
                stack, seen = [root], set()
                while stack:
                    node = stack.pop()
                    if node not in seen:
                        seen.add(node)
                        stack.extend(graph[node])
                reached[root] = seen
            expected = {
                r: (len(seen - {r}), sum(
                    all(v not in reached[other] for other in roots if r != other)
                    for v in seen - {r}
                ))
                for r, seen in reached.items()
            }
            self.assertEqual(count_impacts(graph, roots), (expected, len(set().union(*reached.values()))))

    @unittest.skipUnless(shutil.which("git"), "Git not installed")
    def test_git_head_blob_comparison(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            src = root / "src"
            src.mkdir()
            def git(*args, **kwargs):
                return subprocess.check_output(
                    ["git", "-C", str(root), *args], text=True, stderr=subprocess.DEVNULL, **kwargs
                ).strip()
            git("init", "-q", "--template=")
            for module in ("A", "B", "D"):
                (src / f"{module}.lean").write_text("import Mathlib\n")
            git("add", "src")
            tree = git("write-tree")
            sha = git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                      "commit-tree", tree, input="fixture")
            git("update-ref", "HEAD", sha)
            tracker = MARKDOWN.replace("abcd123401", sha[:10])
            clean = make_report(src, tracker)
            self.assertEqual(clean["revision_status"], "match")
            self.assertEqual(clean["source_lean_file_differences_from_head"], 0)
            (src / "A.lean").write_text("import B\n")
            (src / "D.lean").unlink()
            (src / "Extra.lean").write_text("import B\n")
            dirty = make_report(root, tracker)
            self.assertEqual(dirty["revision_status"], "match")
            self.assertEqual(dirty["source_lean_file_differences_from_head"], 3)
            self.assertTrue(any("Dirty source tree: 3" in w for w in dirty["warnings"]))

    def test_report_missing_target_leaf_and_skew(self):
        with tempfile.TemporaryDirectory() as t:
            t = Path(t)
            (t / "src" / "Dir").mkdir(parents=True)
            for name, source in {
                "A": "import Mathlib",
                "B": "import Mathlib",
                "Dir/C": "import B",
                "D": "import A\nimport B",
                "E": "import A",
                "F": "import B",
                "G": "import A\nimport .Fake",
                "H": "import A",
            }.items():
                if name == "G":
                    source = "import A\nnamespace Foo\nimport NotHeader"
                (t / "src" / (name + ".lean")).write_text(source, encoding="utf-8")
            (t / "Outside.lean").write_text("import A", encoding="utf-8")
            report = make_report(t, MARKDOWN, ["src/Dir/C.lean", "G", "F", "Absent"], "abcd123999")
            self.assertEqual(report["revision_status"], "skew")
            self.assertEqual(report["source_modules"], 8)
            self.assertEqual(report["source_import_edges"], 7)
            self.assertEqual(report["missing_active_roots"], ["Missing"])
            self.assertEqual([row["module"] for row in report["roots"]], ["A", "B", "Dir.C", "Missing"])
            self.assertEqual([(row["affected_downstream"], row["exclusive_affected_downstream"])
                              for row in report["roots"]], [(4, 3), (3, 1), (0, 0), (None, None)])
            self.assertEqual([row["tracker_status"] for row in report["targets"]],
                             ["open_fix_exists", "changed_rebuilding", "not_listed", "not_listed"])
            self.assertEqual([row["source_present"] for row in report["targets"]], [True, True, True, False])
            self.assertEqual(make_report(t / "src", MARKDOWN, source_revision="abcd123401")["revision_status"], "match")
            self.assertEqual(make_report(t, MARKDOWN)["revision_status"], "unverified")
            tracker = t / "PR120-BUGS.md"
            tracker.write_text(MARKDOWN, encoding="utf-8")
            cli = [sys.executable, str(Path(__file__).with_name("pr120_triage.py")),
                   str(t), str(tracker), "--source-revision", "abcd123999", "--format", "json"]
            first = subprocess.check_output(cli)
            self.assertEqual(first, subprocess.check_output(cli))
            self.assertEqual(json.loads(first)["roots"], report["roots"])


if __name__ == "__main__":
    unittest.main()
