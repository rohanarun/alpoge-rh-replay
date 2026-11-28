#!/usr/bin/env python3
"""Tests of cache registration and the baseline fallback in scripts/ci-cache-get.py.

Run as `python3 -I scripts/tests/test_ci_cache_baseline.py`. The baseline tests build a small Git
repository with the project layout and a fake public cache that has records for chosen inputs.
"""
import gzip
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "ci-cache-get.py"
spec = importlib.util.spec_from_file_location("ci_cache_get", SCRIPT)
cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache)

LAKEFILE = 'srcDir = "src"\nname = "T"\n'


def run(root, *args):
    subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True)


def commit(root, files, message):
    for name, text in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    run(root, "add", "-A")
    run(root, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "-m", message)
    return subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()


def publish(store, identity, head):
    """Put a record, map and module manifest for identity into the fake cache store."""
    contents = (json.dumps(cache.SCHEMA) + "\n" + json.dumps(["0123456789abcdef", "0123456789abcdef.ltar"]) + "\n").encode()
    map_sha = cache.digest(contents)
    plain = (json.dumps({"schema": 1, **identity, "input_fingerprint": cache.fingerprint(identity),
                         "map_sha256": map_sha, "modules": 1}) + "\n"
             + json.dumps(["A", "0123456789abcdef", "0123456789abcdef.ltar", "0" * 64]) + "\n").encode()
    buffer = io.BytesIO()
    with gzip.GzipFile(fileobj=buffer, mode="wb", mtime=0) as stream:
        stream.write(plain)
    manifest = buffer.getvalue()
    manifest_sha = cache.digest(manifest)
    record = {"schema": 1, "repository": cache.REPOSITORY, "project": cache.PROJECT, **identity,
              "build_exit_code": 0, "input_fingerprint": cache.fingerprint(identity),
              "candidate_head": head, "candidate_tree": head,
              "map_key": f"{cache.PREFIX}/maps/{map_sha}.jsonl", "map_sha256": map_sha,
              "module_manifest_key": f"{cache.PREFIX}/module-manifests/{manifest_sha}.jsonl.gz",
              "module_manifest_sha256": manifest_sha, "module_manifest_bytes": len(manifest)}
    store[f"{cache.PREFIX}/inputs/{cache.fingerprint(identity)}.json"] = json.dumps(record).encode()
    store[record["map_key"]] = contents
    store[record["module_manifest_key"]] = manifest
    return record


class Registration(unittest.TestCase):
    def test_only_current_package_and_expected_output_count(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            project = root / "outputs" / "GRH"
            other = root / "outputs" / "TauCeti"
            project.mkdir(parents=True)
            other.mkdir()
            artifact = "0123456789abcdef.ltar"
            entries = [(f"{n:016x}", artifact) for n in range(5)]
            output = {"schemaVersion": "2026-02-25", "data": artifact}

            def mapping(package, index):
                return package / (entries[index][0] + ".json")

            mapping(project, 0).write_text(json.dumps(output))
            mapping(other, 1).write_text(json.dumps(output))
            mapping(project, 2).write_text(json.dumps({**output, "scope": artifact,
                                                       "data": "fedcba9876543210.ltar"}))
            mapping(project, 3).write_text('{"data": "' + artifact)
            # The fifth input has never been registered in either package.
            self.assertEqual(cache.registered(root, "GRH", entries), {entries[0][0]})


class Baseline(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name)
        run(self.root, "init", "-q", "-b", "main")
        self.store, self.requests = {}, []
        self.addCleanup(setattr, cache, "BASELINE_FILE", cache.BASELINE_FILE)
        cache.BASELINE_FILE = self.root / "pinned.json"

    def tearDown(self):
        self.directory.cleanup()

    def fetcher(self, key, maximum=cache.MAX_JSON):
        self.requests.append(key)
        return self.store.get(key)

    def base(self):
        return commit(self.root, {"lakefile.toml": LAKEFILE, "lake-manifest.json": "{}\n",
                                  "lean-toolchain": "leanprover/lean4:v4.35.0\n", "src/A.lean": "-- 1\n"}, "base")

    def pin(self, identity):
        cache.BASELINE_FILE.write_text(json.dumps({**identity, "input_fingerprint": cache.fingerprint(identity)}))

    def test_nearest_published_ancestor(self):
        first = self.base()
        published = cache.identity_at(self.root, first, {})
        publish(self.store, published, first)
        commit(self.root, {"src/A.lean": "-- 2\n"}, "unpublished")
        run(self.root, "checkout", "-q", "-b", "pr")
        commit(self.root, {"src/A.lean": "-- 3\n"}, "pull request")
        self.pin(published)
        identity = cache.current_identity(self.root)
        self.assertIsNone(cache.find_record(identity, self.fetcher))
        record, baseline = cache.find_baseline(self.root, identity, "main", 200, self.fetcher)
        self.assertEqual(baseline, published)
        self.assertEqual(record["candidate_head"], first)
        # The baseline's blobs are bound to the baseline's inputs, not to the current ones.
        cache.validated_blobs(record, baseline, self.fetcher)
        with self.assertRaises(ValueError):
            cache.validated_blobs(record, identity, self.fetcher)

    def test_nearest_published_ancestor_for_nested_project(self):
        project = self.root / "grh"
        first = commit(project, {"lakefile.toml": LAKEFILE, "lake-manifest.json": "{}\n",
                                 "lean-toolchain": "leanprover/lean4:v4.37.0-rc1\n",
                                 "src/A.lean": "-- published\n"}, "published nested project")
        published = cache.current_identity(project)
        publish(self.store, published, first)
        older = {**published, "source_tree": "1" * 40}
        publish(self.store, older, "2" * 40)
        commit(project, {"src/A.lean": "-- new source\n"}, "change nested project")
        self.pin(older)

        record, baseline = cache.find_baseline(project, cache.current_identity(project), "main", 200,
                                               self.fetcher)
        self.assertEqual(record["candidate_head"], first)
        self.assertEqual(baseline, published)

    def test_pinned_when_no_ancestor_is_published(self):
        first = self.base()
        pinned = {**cache.identity_at(self.root, first, {}), "source_tree": "1" * 40}
        publish(self.store, pinned, "2" * 40)
        self.pin(pinned)
        commit(self.root, {"src/A.lean": "-- 2\n"}, "change")
        identity = cache.current_identity(self.root)
        record, baseline = cache.find_baseline(self.root, identity, "main", 200, self.fetcher)
        self.assertEqual(baseline, pinned)
        self.assertEqual(record["candidate_head"], "2" * 40)

    def test_other_toolchain_or_manifest_is_never_a_baseline(self):
        first = self.base()
        publish(self.store, cache.identity_at(self.root, first, {}), first)
        self.pin(cache.identity_at(self.root, first, {}))
        commit(self.root, {"lake-manifest.json": '{"changed": true}\n', "src/A.lean": "-- 2\n"}, "bump")
        identity = cache.current_identity(self.root)
        self.assertEqual(cache.find_baseline(self.root, identity, "main", 200, self.fetcher), (None, None))
        self.assertEqual(self.requests, [])

    def test_missing_ref_still_tries_the_pinned_record(self):
        first = self.base()
        published = cache.identity_at(self.root, first, {})
        publish(self.store, published, first)
        self.pin(published)
        commit(self.root, {"src/A.lean": "-- 2\n"}, "change")
        identity = cache.current_identity(self.root)
        record, baseline = cache.find_baseline(self.root, identity, "origin/main", 200, self.fetcher)
        self.assertEqual(baseline, published)

    def test_pinned_file_must_match_its_fingerprint(self):
        self.base()
        identity = cache.identity_at(self.root, "HEAD", {})
        cache.BASELINE_FILE.write_text(json.dumps({**identity, "input_fingerprint": "0" * 64}))
        with self.assertRaises(ValueError):
            cache.pinned_identity(cache.BASELINE_FILE)


if __name__ == "__main__":
    unittest.main()
