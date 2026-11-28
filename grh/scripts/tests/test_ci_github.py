"""Exercise build discovery with the API responses seen by the cache publisher."""
import argparse
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "ci-github.py"
spec = importlib.util.spec_from_file_location("ci_github", SCRIPT)
ci = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ci)

SHA = "a" * 40
RUN = {"id": 7, "run_attempt": 1, "repository": {"full_name": ci.REPOSITORY},
       "path": ci.WORKFLOW, "head_sha": SHA, "event": "push", "head_branch": "main",
       "status": "completed", "conclusion": "success"}


class Discovery(unittest.TestCase):
    def test_wait_for_main_build_to_appear(self):
        args = argparse.Namespace(sha=SHA, run_id=None, wait_minutes=2)
        pages = [[], [dict(RUN, id=6, event="pull_request")],
                 [dict(RUN, status="in_progress", conclusion=None)], [RUN]]
        with patch.object(ci, "runs", side_effect=pages), patch.object(ci.time, "sleep") as sleep, \
                patch.object(ci, "api", side_effect=[
                    {"jobs": [{"name": ci.JOB, "conclusion": "success", "labels": [ci.LABEL]}]},
                    {"artifacts": [{"name": f"cache-{SHA}", "expired": False}]}]), \
                patch.object(ci, "outputs") as output:
            ci.find_run(args)
        self.assertEqual(sleep.call_count, 3)
        output.assert_called_once_with(run_id=7, artifact=f"cache-{SHA}", event="push")

    def test_no_wait_or_definitive_failure(self):
        for minutes, rows in [(0, []), (90, [dict(RUN, conclusion="failure")])]:
            with self.subTest(minutes=minutes), patch.object(ci, "runs", return_value=rows), \
                    patch.object(ci.time, "sleep") as sleep:
                with self.assertRaisesRegex(ValueError, "no successful self-hosted build"):
                    ci.find_run(argparse.Namespace(sha=SHA, run_id=None, wait_minutes=minutes))
                sleep.assert_not_called()

    def test_missing_run_respects_deadline(self):
        args = argparse.Namespace(sha=SHA, run_id=7, wait_minutes=1)
        with patch.object(ci, "runs", return_value=[]), \
                patch.object(ci.time, "monotonic", side_effect=[100, 150, 160]), \
                patch.object(ci.time, "sleep") as sleep:
            with self.assertRaisesRegex(ValueError, "no successful self-hosted build"):
                ci.find_run(args)
        sleep.assert_called_once_with(10)


if __name__ == "__main__":
    unittest.main()
