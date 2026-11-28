import hashlib
import importlib.util
import json
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import subprocess
import sys
import tempfile
from threading import Event
import unittest
from unittest.mock import patch


SCRIPT = Path(__file__).resolve().parents[1] / "fetch-artifacts.py"
spec = importlib.util.spec_from_file_location("fetch_artifacts", SCRIPT)
fetcher = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fetcher)


class CacheRefresh(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        self.name = "0123456789abcdef.ltar"
        self.artifact = root / "artifacts" / self.name
        self.artifact.parent.mkdir()
        self.artifact.write_bytes(b"corrupt")
        self.valid = b"verified artifact"
        digests = root / "sha256.json"
        digests.write_text(json.dumps({self.name: hashlib.sha256(self.valid).hexdigest()}))
        mapping = root / "map.jsonl"
        mapping.write_text("{}\n" + json.dumps([self.name[:-5], self.name]) + "\n")
        self.report = root / "report.json"
        self.argv = [str(SCRIPT), str(mapping), str(root), "--verify-existing",
                     "--sha256", str(digests), "--report", str(self.report)]
        limit = patch.object(fetcher.resource, "getrlimit", return_value=(65536, 65536))
        limit.start()
        self.addCleanup(limit.stop)

    def fetch(self):
        with self.assertRaises(SystemExit) as result:
            fetcher.main()
        return result.exception.code

    def test_late_refresh_preserves_another_restore(self):
        first_hash_read = Event()
        peer_finished = Event()
        real_sha256 = fetcher.sha256

        def pause_first_hash(path):
            digest = real_sha256(path)
            if path == self.artifact and not first_hash_read.is_set():
                first_hash_read.set()
                if not peer_finished.wait(timeout=10):
                    raise TimeoutError("second restore did not finish")
            return digest

        def download(args, **kwargs):
            if peer_finished.is_set():
                return subprocess.CompletedProcess(args, 37, stderr="curl: (37) source unavailable")
            config = Path(args[args.index("--config") + 1]).read_text()
            output = next(line for line in config.splitlines() if line.startswith("output = "))
            Path(json.loads(output.removeprefix("output = "))).write_bytes(self.valid)
            return subprocess.CompletedProcess(args, 0, stderr="")

        with (patch.object(sys, "argv", self.argv),
              patch.object(fetcher, "sha256", side_effect=pause_first_hash),
              patch.object(fetcher.subprocess, "run", side_effect=download),
              ThreadPoolExecutor(2) as pool):
            first = pool.submit(self.fetch)
            try:
                self.assertTrue(first_hash_read.wait(timeout=5))
                self.assertEqual(pool.submit(self.fetch).result(timeout=5), 0)
                self.assertEqual(self.artifact.read_bytes(), self.valid)
            finally:
                peer_finished.set()
            self.assertEqual(first.result(timeout=5), 0)
        self.assertEqual(self.artifact.read_bytes(), self.valid)

    def test_failed_refresh_leaves_a_cache_miss_for_lake(self):
        failure = subprocess.CompletedProcess([], 37, stderr="curl: (37) source unavailable")
        with patch.object(sys, "argv", self.argv), patch.object(fetcher.subprocess, "run", return_value=failure):
            self.assertEqual(self.fetch(), 1)
        self.assertFalse(self.artifact.exists())
        self.assertEqual(json.loads(self.report.read_text())["curl_exit"], 37)


if __name__ == "__main__":
    unittest.main()
