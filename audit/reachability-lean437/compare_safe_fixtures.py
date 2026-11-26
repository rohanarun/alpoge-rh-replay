#!/usr/bin/env python3
"""Twelve safe differential fixtures against pinned stock leanexport."""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
import pathlib
import shlex
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
PIN = "0b77e12952ad39077d80d8bd6b66d601f225c321"
SUITE = "reachability-safe12/1"
MODULE = "ReachabilityFixtures"
KINDS = ("axiom", "definition", "opaque", "theorem", "quotient", "inductive", "constructor", "recursor")
DECL_TAGS = {"axiom": "axiom", "def": "definition", "opaque": "opaque", "thm": "theorem", "quot": "quotient"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def atomic_json(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def parse_export(path):
    """Parse declaration identities, not pretty names; expand grouped inductives."""
    names = {0: ()}
    declarations = {}
    expression_tags = collections.Counter()
    nat_literals, string_literals = set(), set()
    metadata = None

    def add(data, kind):
        name = names[data["name"]]
        require(name not in declarations, f"duplicate exported declaration: {name!r}")
        declarations[name] = kind

    with path.open(encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            record = json.loads(line)
            if "meta" in record:
                require(metadata is None, "duplicate export metadata")
                metadata = record["meta"]
            elif "in" in record:
                index = record["in"]
                require(index not in names, f"duplicate name index {index}")
                if "str" in record:
                    row = record["str"]
                    names[index] = names[row["pre"]] + (row["str"],)
                else:
                    row = record["num"]
                    names[index] = names[row["pre"]] + (row["i"],)
            elif "ie" in record:
                for tag in record.keys() - {"ie"}:
                    expression_tags[tag] += 1
                if "natVal" in record:
                    nat_literals.add(record["natVal"])
                if "strVal" in record:
                    string_literals.add(record["strVal"])
            elif "il" in record:
                pass
            elif "inductive" in record:
                for key, kind in (("types", "inductive"), ("ctors", "constructor"), ("recs", "recursor")):
                    for row in record["inductive"][key]:
                        add(row, kind)
            else:
                tags = record.keys() & DECL_TAGS.keys()
                require(len(tags) == 1, f"unknown export record at line {line_number}")
                tag = next(iter(tags))
                add(record[tag], DECL_TAGS[tag])
    require(metadata is not None and metadata["lean"]["githash"] == PIN, "wrong export Lean identity")
    require(metadata["format"]["version"] == "3.1.0", "unexpected export format")
    return declarations, expression_tags, nat_literals, string_literals


def parse_helper(names_path, report_path):
    report = json.loads(report_path.read_text())
    require(report["schema"] == "rh-reachable-declarations/1", "wrong helper schema")
    require(report["leanCommit"] == PIN, "wrong helper Lean identity")
    require(report["independentProofValidation"] is False, "mislabelled metric")
    require(report["expressionNodeCount"] is None, "unsupported expression-node claim")
    declarations, display_names = {}, []
    with names_path.open(encoding="utf-8") as stream:
        for line in stream:
            row = json.loads(line)
            name = tuple(row["components"])
            require(name not in declarations, f"duplicate helper declaration: {name!r}")
            require(row["kind"] in KINDS, "invalid declaration kind")
            declarations[name] = row["kind"]
            display_names.append(row["name"])
    require(display_names == sorted(display_names), "helper output is not sorted")
    counts = collections.Counter(declarations.values())
    require(report["reachableDeclarationCount"] == len(declarations), "wrong helper count")
    require(report["declarationCounts"] == {kind: counts[kind] for kind in KINDS}, "wrong kind counts")
    return declarations, report


def check_case(case, actual, expressions, nats, strings):
    for name in case.get("required", []):
        require(tuple(name.split(".")) in actual, f"{case['name']}: missing fixture witness {name}")
    for name in case.get("forbidden", []):
        require(tuple(name.split(".")) not in actual, f"{case['name']}: spurious dependency {name}")
    for suffix in case.get("required_suffixes", []):
        suffix = tuple(suffix)
        require(any(name[-len(suffix):] == suffix and name[0] == "_private" for name in actual),
                f"{case['name']}: private dependency was not retained: {suffix}")
    for tag in case.get("required_expression_tags", []):
        require(expressions[tag] > 0, f"fixture did not exercise expression tag {tag}")
    if "required_nat_literal" in case:
        require(case["required_nat_literal"] in nats, "fixture did not retain its Nat literal")
    if "required_string_literal" in case:
        require(case["required_string_literal"] in strings, "fixture did not retain its string literal")
    if "expected_count" in case:
        require(len(actual) == case["expected_count"], "unexpected fixture declaration count")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain-dir", type=pathlib.Path, required=True)
    parser.add_argument("--output-dir", type=pathlib.Path, required=True)
    parser.add_argument("--timeout", type=int, default=180, help="seconds per small fixture command")
    parser.add_argument("--yes", action="store_true", help="run the displayed commands without prompting")
    args = parser.parse_args()
    require(args.timeout > 0, "timeout must be positive")
    toolchain, output = args.toolchain_dir.resolve(), args.output_dir.resolve()
    lean, exporter = toolchain / "bin/lean", toolchain / "bin/leanexport"
    require(lean.is_file() and exporter.is_file(), "toolchain must provide lean and stock leanexport")
    sources = [HERE / "ReachableDecls.lean", HERE / "fixtures/ReachabilityFixtures.lean", HERE / "fixtures/cases.json",
               HERE / "compare_safe_fixtures.py"]
    fingerprints = {str(path.relative_to(HERE)): sha(path) for path in sources}
    report_path = output / "safe12-fixture-report.json"
    if output.exists():
        previous = json.loads(report_path.read_text()) if report_path.exists() else {}
        require(previous.get("result") == "complete" and previous.get("fixture_suite") == SUITE
                and previous.get("sources") == fingerprints
                and previous.get("lean_binary_sha256") == sha(lean)
                and previous.get("exporter_binary_sha256") == sha(exporter),
                "output directory already exists without a matching completed receipt; choose a fresh directory")
        for case in previous["cases"]:
            for suffix, key in (("names.jsonl", "names_sha256"), ("export", "reference_export_sha256"), ("json", "summary_sha256")):
                require(sha(output / f"{case['name']}.{suffix}") == case[key],
                        f"completed fixture artifact changed: {case['name']}.{suffix}")
        print(json.dumps({"result": "already_complete", "report": str(report_path)}))
        return
    output.mkdir(parents=True)
    env = {key: value for key, value in os.environ.items() if not key.startswith(("LEAN_", "LAKE_"))}
    env.update(PATH=str(toolchain / "bin") + os.pathsep + env.get("PATH", os.defpath),
               LEAN_PATH=str(output), LEAN_ABORT_ON_PANIC="1")
    state = {"result": "running", "fixture_suite": SUITE, "lean_commit": PIN, "sources": fingerprints,
             "lean_binary_sha256": sha(lean), "exporter_binary_sha256": sha(exporter), "cases": [], "commands": []}
    atomic_json(report_path, state)

    def run(label, command, *, stdout=None, expect_success=True):
        command = list(map(str, command))
        print(f"{label}\n$ {shlex.join(command)}", flush=True)
        if not args.yes:
            choice = input("Proceed / skip / abort? [p/s/a] ").strip().lower()
            require(choice in ("p", "proceed"), "fixture command skipped/aborted; no passing receipt will be issued")
        error_path = output / f"{label}.stderr"
        output_path = stdout or output / f"{label}.stdout"
        with output_path.open("wb") as out, error_path.open("wb") as err:
            result = subprocess.run(command, cwd=HERE / "fixtures", env=env, stdout=out,
                                    stderr=err, timeout=args.timeout, check=False)
        row = {"label": label, "exit_code": result.returncode, "stdout": output_path.name,
               "stderr": error_path.name, "expected_success": expect_success}
        state["commands"].append(row)
        atomic_json(report_path, state)
        require((result.returncode == 0) == expect_success, f"{label}: unexpected exit {result.returncode}; inspect {error_path}")

    helper = HERE / "ReachableDecls.lean"
    try:
        run("compile-fixtures", [lean, "-o", output / f"{MODULE}.olean", "-i", output / f"{MODULE}.ilean",
                                 "-c", output / f"{MODULE}.c", HERE / "fixtures/ReachabilityFixtures.lean"])
        cases = json.loads((HERE / "fixtures/cases.json").read_text())
        for case in cases:
            label = case["name"]
            targets_path, names_path = output / f"{label}.targets", output / f"{label}.names.jsonl"
            summary_path, export_path = output / f"{label}.json", output / f"{label}.export"
            targets_path.write_text("\n".join(case["targets"]) + "\n")
            run(f"{label}-reference", [exporter, MODULE, *case.get("export_options", []), "--", *case["targets"]], stdout=export_path)
            run(f"{label}-helper", [lean, "--run", helper, MODULE, targets_path, names_path, *case.get("helper_options", [])], stdout=summary_path)
            expected, expressions, nats, strings = parse_export(export_path)
            actual, summary = parse_helper(names_path, summary_path)
            require(actual == expected,
                    f"{label}: closure mismatch; missing={list(expected.keys() - actual.keys())[:5]!r}; "
                    f"extra={list(actual.keys() - expected.keys())[:5]!r}")
            check_case(case, actual, expressions, nats, strings)
            require(summary["targetsText"] == targets_path.read_text(), "targets provenance mismatch")
            state["cases"].append({"name": label, "result": "complete", "reachable_declarations": len(actual),
                                   "names_sha256": sha(names_path), "reference_export_sha256": sha(export_path),
                                   "summary_sha256": sha(summary_path)})
            atomic_json(report_path, state)
        # Same roots, new destination: both summaries and sorted names must be byte-deterministic.
        first = cases[0]["name"]
        run("determinism", [lean, "--run", helper, MODULE, output / f"{first}.targets", output / "repeat.names.jsonl"],
            stdout=output / "repeat.json")
        require((output / "repeat.names.jsonl").read_bytes() == (output / f"{first}.names.jsonl").read_bytes(), "names are nondeterministic")
        require((output / "repeat.json").read_bytes() == (output / f"{first}.json").read_bytes(), "summary is nondeterministic")
        missing = output / "missing.targets"
        missing.write_text("ReachabilityFixtures.doesNotExist\n")
        run("missing-root-reference", [exporter, MODULE, "--", "ReachabilityFixtures.doesNotExist"], expect_success=False)
        run("missing-root-helper", [lean, "--run", helper, MODULE, missing, output / "missing.names.jsonl"], expect_success=False)
        empty = output / "empty.targets"
        empty.write_text("")
        run("empty-roots", [lean, "--run", helper, MODULE, empty, output / "empty.names.jsonl"], expect_success=False)
        run("unsupported-option", [lean, "--run", helper, MODULE, missing, output / "option.names.jsonl", "--ignore-missing"], expect_success=False)
        before = sha(output / "repeat.names.jsonl")
        run("refuse-overwrite", [lean, "--run", helper, MODULE, output / f"{first}.targets", output / "repeat.names.jsonl"], expect_success=False)
        require(sha(output / "repeat.names.jsonl") == before, "existing names output was changed")
        require({str(path.relative_to(HERE)): sha(path) for path in sources} == fingerprints, "fixture sources changed during comparison")
        state.update(result="complete", independent_proof_validation=False, helper_compiled_and_differentially_checked=True)
        atomic_json(report_path, state)
        print(json.dumps({"result": "complete", "report": str(report_path), "cases": len(cases)}))
    except BaseException as error:
        state.update(result="failed", error=str(error))
        atomic_json(report_path, state)
        raise


if __name__ == "__main__":
    main()
