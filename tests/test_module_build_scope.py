import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "module-build-scope.py"
spec = importlib.util.spec_from_file_location("module_build_scope", SCRIPT)
scope = importlib.util.module_from_spec(spec)
spec.loader.exec_module(scope)


class ModuleBuildScopeTests(unittest.TestCase):
    @patch.object(scope.subprocess, "check_output", return_value=b"src/A.lean\0src/B.lean\0")
    def test_partial_checkout_does_not_hide_importers(self, _read_index):
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp)
            (repo / ".git").mkdir()
            (repo / "src").mkdir()
            (repo / "src/A.lean").touch()
            with self.assertRaisesRegex(ValueError, "tracked sources missing"):
                scope.source_files(repo)

    def test_transitive_counts_deduplicate_diamonds_and_list_direct_importers(self):
        graph = {"A": {"B", "C"}, "B": {"G.Δ₂"}, "C": {"G.Δ₂"}, "G.Δ₂": set(), "D": {"A"}}
        self.assertEqual(scope.scope_rows(graph, {"A", "G.Δ₂"}),
                         [(1, "G.Δ₂", ["B", "C"]), (4, "A", ["D"])])

    @patch.object(scope.subprocess, "run")
    def test_header_protocol_and_batches(self, run):
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp)
            (repo / "src" / "G").mkdir(parents=True)
            for path in ["G/Base.lean", "G/Δ₂.lean", "Main.lean"]:
                (repo / "src" / path).touch()
            files = scope.source_files(repo)
            headers = {"src/Main.lean": [dict(module="G.Δ₂", isExported=True, importAll=True)],
                       "src/G/Δ₂.lean": [dict(module="G.Base", isMeta=True), dict(module="Mathlib")],
                       "src/G/Base.lean": [dict(module="Init")]}

            def response(command, *, cwd, input, **kwargs):
                self.assertEqual(command, ["lean", "--deps-json", "--stdin"])
                self.assertEqual(cwd, repo)
                paths = input.decode("utf-8").splitlines()
                self.assertLessEqual(len(paths), 2)
                rows = [{"errors": [], "result": {"imports": headers[path]}} for path in paths]
                return scope.subprocess.CompletedProcess(command, 0, json.dumps({"imports": rows}).encode())

            run.side_effect = response
            with patch.object(scope, "BATCH_SIZE", 2):
                graph = scope.project_graph(repo, "lean", files)
            self.assertEqual(run.call_count, 2)
            self.assertEqual(scope.scope_rows(graph, {"Main"}), [(3, "Main", [])])

    @patch.object(scope.subprocess, "run")
    def test_failed_or_missing_file_result_is_an_error(self, run):
        for rows, expected in [([{"errors": ["bad header"]}], "bad header"), ([], "number of file headers")]:
            with self.subTest(rows=rows):
                run.return_value.stdout = json.dumps({"imports": rows}).encode()
                with self.assertRaisesRegex(ValueError, expected):
                    list(scope.parse_batch(Path("."), "lean", ["src/Main.lean"]))

    def test_missing_project_import_and_cycle_are_errors(self):
        files = {"G.A": "src/G/A.lean"}
        for imports, error in [({"G.Missing"}, "missing project import"), ({"G.A"}, "cycle")]:
            with self.subTest(imports=imports), patch.object(scope, "parse_batch", return_value=[imports]):
                with self.assertRaisesRegex(ValueError, error):
                    scope.project_graph(Path("."), "lean", files)


if __name__ == "__main__":
    unittest.main()
