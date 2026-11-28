"""Local file handling for the cache publisher, without contacting the object store."""
import importlib.util
import os
from pathlib import Path
import tempfile
import tracemalloc
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "publish-ci-cache.py"
spec = importlib.util.spec_from_file_location("publish_ci_cache", SCRIPT)
publisher = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publisher)


class RegularFile(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.path = Path(tmp.name) / "artifact"

    def test_small_artifact_with_large_size_limit(self):
        data = b"a" * 4096
        self.path.write_bytes(data)
        tracemalloc.start()
        try:
            self.assertEqual(publisher.regular(self.path, 32 << 20), data)
            _, peak = tracemalloc.get_traced_memory()
        finally:
            tracemalloc.stop()
        self.assertLess(peak, 1 << 20)

    def test_empty_exact_and_oversize(self):
        for data in (b"", b"abc"):
            self.path.write_bytes(data)
            self.assertEqual(publisher.regular(self.path, len(data)), data)
        with self.assertRaisesRegex(ValueError, "bounded regular file"):
            publisher.regular(self.path, 2)

    def test_size_change_during_read(self):
        fstat = os.fstat
        for changed in (b"short", b"a longer archive"):
            with self.subTest(changed=changed):
                self.path.write_bytes(b"original")

                def resize(fd):
                    before = fstat(fd)
                    self.path.write_bytes(changed)
                    return before

                with patch.object(os, "fstat", side_effect=resize):
                    with self.assertRaisesRegex(ValueError, "size changed"):
                        publisher.regular(self.path, 100)


if __name__ == "__main__":
    unittest.main()
