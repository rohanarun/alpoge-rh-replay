"""Cache downloads and checksum checks in a process with a small file limit."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "fetch-artifacts.py"


class FileLimit(unittest.TestCase):
    @unittest.skipUnless(os.name == "posix", "uses the POSIX open-file limit")
    def test_fetch_and_recheck_with_24_descriptors(self):
        import resource

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            public = root / "public"
            public.mkdir()
            mapping, digests, report = (root / name for name in ("map", "sha256", "report"))
            rows, shas = [], {}
            for i in range(64):
                key = f"{i:016x}"
                name = key + ".ltar"
                data = bytes([i]) * (256 * 1024)
                (public / (key + ".art")).write_bytes(data)
                rows.append([key, name])
                shas[name] = hashlib.sha256(data).hexdigest()
            mapping.write_text("\n".join(json.dumps(row) for row in ["2026-03-17", *rows]) + "\n")
            digests.write_text(json.dumps(shas))
            cmd = [sys.executable, "-I", str(SCRIPT), str(mapping), str(root / "cache"),
                   "--base-url", public.as_uri() + "/", "--sha256", str(digests),
                   "--verify-existing", "--report", str(report)]
            for missing in (len(rows), 0):
                with self.subTest(missing=missing):
                    result = subprocess.run(
                        cmd, capture_output=True, text=True, timeout=30,
                        preexec_fn=lambda: resource.setrlimit(resource.RLIMIT_NOFILE, (24, 24)))
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertIn(f"{missing} missing locally", result.stdout)
                    self.assertEqual(json.loads(report.read_text()),
                                     {"curl_exit": 0, "curl_errors": [], "sha256_mismatches": 0})


if __name__ == "__main__":
    unittest.main()
