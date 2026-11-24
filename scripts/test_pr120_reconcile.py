import unittest

from pr120_reconcile import BRANCH, REPO, parse_tracker, reconcile


class ReconcileTest(unittest.TestCase):
    def test_tracker_only_open(self):
        tracker = "head `abc1234`\n## Open (2)\n| `α/A.lean:2` | | claimed: #12 |\n| `α/A.lean:8:2` | | |\n## Changed\n| `C.lean:5` | | |"
        self.assertEqual(parse_tracker(tracker), ("abc1234", {"src/α/A.lean": {"lines": [2, 8], "tracker_prs": [12]}}))
        with self.assertRaises(ValueError):
            parse_tracker(tracker.replace("Open (2)", "Open (3)"))

    def test_changed_removed_overlap_and_unknown(self):
        names = [f"src/{k}.lean" for k in "ABCDE"]
        rows = {n: {"lines": [1], "tracker_prs": []} for n in names}
        old = dict(zip(names, ["a", "b", "c", "d"]))
        new = dict(zip(names, ["x", "b", "c", "d"]))
        del new[names[2]]
        snapshot = {"base": BRANCH, "repository": REPO, "listing_complete": True,
                    "pulls": [{"files": [names[1]], "number": 1}]}
        result, _ = reconcile(rows, old, new, snapshot)
        self.assertEqual([r["status"] for r in result], [
            "changed-recheck", "unchanged-overlap", "removed-since-tracker",
            "unchanged-reproduce-first", "missing-at-tracker-commit",
        ])
        self.assertEqual(result[0]["open_pr_overlaps"], [])
        partial, _ = reconcile(rows, old, new, {**snapshot, "listing_complete": False})
        self.assertIsNone(partial[0]["open_pr_overlaps"])
        self.assertEqual(partial[1]["open_pr_overlaps"], [1])
        result, warnings = reconcile(rows, old, new, None)
        self.assertIsNone(result[1]["open_pr_overlaps"])
        self.assertIn("unknown", warnings[0])

    def test_partial_and_wrong_base(self):
        snapshot = {"base": BRANCH, "repository": REPO, "pulls": [{"files": [], "number": 17, "errors": ["timeout"]}]}
        _, warnings = reconcile({}, {}, {}, snapshot)
        self.assertTrue(any("#17" in warning for warning in warnings))
        with self.assertRaises(ValueError):
            reconcile({}, {}, {}, {**snapshot, "base": "main"})


if __name__ == "__main__":
    unittest.main()
