#!/usr/bin/env python3
"""Count project sources in each target's import closure using Lean's header parser."""

import argparse
from collections import defaultdict
from graphlib import TopologicalSorter
import json
import os
from pathlib import Path
import subprocess
import sys


BATCH_SIZE = 512


def raise_walk_error(error):
    raise error


def source_files(repo):
    files = {}
    for directory, _, names in os.walk(repo / "src", onerror=raise_walk_error):
        for name in names:
            if not name.endswith(".lean"):
                continue
            path = (Path(directory) / name).relative_to(repo)
            if "\n" in str(path) or "\r" in str(path):
                raise ValueError(f"line break in source path {path!r}")
            module = ".".join(path.with_suffix("").parts[1:])
            if module in files:
                raise ValueError(f"ambiguous module path: {path} and {files[module]}")
            files[module] = path.as_posix()
    if not files:
        raise ValueError(f"no Lean source files under {repo / 'src'}")
    if (repo / ".git").exists():
        index = subprocess.check_output(["git", "ls-files", "-z", "--", "src"], cwd=repo)
        tracked = {os.fsdecode(item) for item in index.split(b"\0") if item.endswith(b".lean")}
        missing = tracked.difference(files.values())
        if missing:
            raise ValueError(f"incomplete proof checkout: {len(missing)} tracked sources missing, "
                             f"including {min(missing)}")
    return files


def parse_batch(repo, lean, paths):
    result = subprocess.run([lean, "--deps-json", "--stdin"], cwd=repo,
                            input="".join(path + "\n" for path in paths).encode("utf-8"),
                            stdout=subprocess.PIPE, check=True)
    rows = json.loads(result.stdout)["imports"]
    if not isinstance(rows, list) or len(rows) != len(paths):
        raise ValueError("Lean returned an unexpected number of file headers")
    for path, row in zip(paths, rows):
        # Lean can exit successfully even when one file failed to parse.
        if row["errors"]:
            raise ValueError(f"{path}: {'; '.join(row['errors'])}")
        imports = row["result"]["imports"]
        if not isinstance(imports, list):
            raise ValueError(f"{path}: invalid import list")
        names = {entry["module"] for entry in imports}
        if any(not isinstance(name, str) or not name for name in names):
            raise ValueError(f"{path}: invalid imported module name")
        yield names


def project_graph(repo, lean, files):
    modules = sorted(files)
    project_roots = {name.split(".", 1)[0] for name in modules}
    graph = {}
    for start in range(0, len(modules), BATCH_SIZE):
        batch = modules[start:start + BATCH_SIZE]
        headers = parse_batch(repo, lean, [files[module] for module in batch])
        for module, imports in zip(batch, headers):
            missing = sorted(name for name in imports if name.split(".", 1)[0] in project_roots
                             and name not in files)
            if missing:
                raise ValueError(f"{files[module]}: missing project import {missing[0]}")
            graph[module] = {name for name in imports if name in files}
    TopologicalSorter(graph).prepare()  # A cyclic import graph cannot describe a build.
    return graph


def scope_rows(graph, targets):
    importers = defaultdict(list)
    for module, imports in graph.items():
        for dependency in imports:
            if dependency in targets:
                importers[dependency].append(module)
    rows = []
    for target in targets:
        visited = set()
        pending = [target]
        while pending:
            name = pending.pop()
            if name not in visited:
                visited.add(name)
                pending.extend(graph[name])
        rows.append((len(visited), target, sorted(importers[target])))
    return sorted(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd(), help="proof checkout containing src/")
    parser.add_argument("--lean", default="lean", help="Lean executable (default: lean in the proof checkout)")
    parser.add_argument("--list-importers", action="store_true", help="append direct importer names as a JSON array")
    parser.add_argument("targets", nargs="+", help="dotted module names or checkout-relative src/*.lean paths")
    args = parser.parse_args()
    repo = args.repo.resolve()
    files = source_files(repo)
    by_path = {path: module for module, path in files.items()}
    targets = set()
    for arg in args.targets:
        module = by_path.get(Path(arg).as_posix(), arg)
        if module not in files:
            parser.error(f"unknown project target {arg!r}")
        targets.add(module)
    pin = (repo / "lean-toolchain").read_text(encoding="utf-8").strip()
    if pin != "leanprover/lean4:v4.36.0":
        parser.error(f"expected the Lean 4.36.0 proof checkout, found {pin!r}")
    version = subprocess.check_output([args.lean, "--version"], cwd=repo, encoding="utf-8")
    if "version 4.36.0," not in version:
        parser.error(f"expected Lean 4.36.0, found {version.strip()!r}")
    rows = scope_rows(project_graph(repo, args.lean, files), targets)
    print("project_sources\tdirect_importers\tmodule" + ("\timporter_names" if args.list_importers else ""))
    for count, target, importers in rows:
        fields = [str(count), str(len(importers)), target]
        if args.list_importers:
            fields.append(json.dumps(importers, ensure_ascii=False))
        print("\t".join(fields))


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as exc:
        sys.exit(f"module-build-scope: {exc}")
