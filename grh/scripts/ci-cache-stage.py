#!/usr/bin/env python3
"""Stage a finished build's cache outputs for publication, in the build job (no credential).

usage: ci-cache-stage.py <outputs.jsonl> <stage-dir> [--project DIR]

<outputs.jsonl> is the map that `lake build -o` wrote. The stage directory gets:

- outputs.jsonl: that map, restricted to the modules under src (one entry per module);
- modules.jsonl.gz: the module manifest (header bound to the build inputs and the map; one row
  [module, input hash, artifact, SHA-256] per module), as scripts/ci-cache-get.py reads it;
- artifacts/<hash16>.ltar: only the artifacts that the public cache does not have yet.

Adapted from the staging step of the hand publisher (stage.py on the rh-buildq hosts). Nothing
here is trusted: .github/workflows/publish-ci-cache.yml checks all of it again with the code of
main (scripts/publish-ci-cache.py) before anything is published.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

spec = importlib.util.spec_from_file_location("ci_cache_get", Path(__file__).with_name("ci-cache-get.py"))
cli = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cli)


def canonical_line(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("outputs", type=Path)
    parser.add_argument("stage", type=Path)
    parser.add_argument("--project", type=Path, default=Path.cwd())
    args = parser.parse_args()
    root = args.project.resolve()
    identity = cli.current_identity(root)
    listed = cli.source_paths(root, identity["source_tree"])
    names = sorted(path[:-5].replace("/", ".") for path in listed if path.endswith(".lean"))
    lines = args.outputs.read_bytes().splitlines()
    if not lines or cli.decode(lines[0]) != cli.SCHEMA:
        raise ValueError("unexpected Lake output map schema")
    mapping = {}
    for line in lines[1:]:
        key, artifact = cli.decode(line)
        if not cli.HASH.fullmatch(key) or not cli.ARTIFACT.fullmatch(artifact) or key in mapping:
            raise ValueError("invalid or duplicate Lake output map entry")
        mapping[key] = artifact
    build = root / ".lake/build"
    rows, entries, files = [], {}, {}
    for name in names:
        module = Path(*name.split("."))
        trace = json.loads((build / "lib/lean" / module).with_suffix(".trace").read_text())
        input_hash = trace["depHash"]
        if input_hash not in mapping or input_hash in entries:
            raise ValueError(f"{name}: its input hash is not (uniquely) in the build's output map")
        artifact = mapping[input_hash]
        path = (build / "ir" / module).with_suffix(".ltar")
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"{name}: no {path.relative_to(root)}")
        sha256 = hashlib.sha256(path.read_bytes()).hexdigest()
        if files.setdefault(artifact, (path, sha256))[1] != sha256:
            raise ValueError(f"{artifact}: two modules have different bytes for one artifact")
        entries[input_hash] = artifact
        rows.append([name, input_hash, artifact, sha256])
    extra = len(mapping) - len(entries)
    contents = (json.dumps(cli.SCHEMA) + "\n").encode() + b"".join(
        (json.dumps([key, entries[key]], separators=(",", ":")) + "\n").encode() for key in sorted(entries))
    header = {"schema": 1, **identity, "map_sha256": cli.digest(contents),
              "input_fingerprint": cli.fingerprint(identity), "modules": len(rows)}
    manifest = gzip.compress(canonical_line(header) + b"".join(
        (json.dumps(row, separators=(",", ":")) + "\n").encode() for row in sorted(rows)), mtime=0)
    with ThreadPoolExecutor(32) as pool:
        public = dict(zip(files, pool.map(cli.published, files)))
    new = sorted(artifact for artifact, present in public.items() if present is not True)
    args.stage.mkdir(parents=True)
    (args.stage / "artifacts").mkdir()
    (args.stage / "outputs.jsonl").write_bytes(contents)
    (args.stage / "modules.jsonl.gz").write_bytes(manifest)
    for artifact in new:
        shutil.copyfile(files[artifact][0], args.stage / "artifacts" / artifact)
    print(json.dumps({"modules": len(rows), "artifacts": len(files), "new_artifacts": len(new),
                      "unknown_artifacts": sum(present is None for present in public.values()),
                      "other_map_entries_dropped": extra, "input_fingerprint": header["input_fingerprint"],
                      "map_sha256": header["map_sha256"], "module_manifest_sha256": cli.digest(manifest)}))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, subprocess.CalledProcessError) as error:
        sys.exit(f"Staging the cache outputs stopped: {error}")
