# Declaration reachability for Lean 4.37

`ReachableDecls.lean` measures the compiled declaration closure of an explicit list of roots.
It follows the declaration dependencies used by the stock `leanexport` at Lean commit
[`0b77e12952ad39077d80d8bd6b66d601f225c321`](https://github.com/leanprover/lean4/tree/0b77e12952ad39077d80d8bd6b66d601f225c321)
(4.37.0-rc1), and emits declaration names and kinds without constructing the exporter's
global expression serialization tables.

This is an opt-in measurement tool. Its compiler pin is separate from this repository's
historical Lean 4.33.1 replay and the current Lean 4.36 consolidation campaign. It is not
part of `verify.sh`, the volunteer tracker, or the default CI workflow.

**Validation status:** all 12 safe differential cases passed on x86-64 Linux with the exact
pinned compiler and exporter. The [completed receipt](safe12-fixture-report.json) records
the four tested source hashes, compiler/exporter hashes, exact name/kind comparisons and
result fingerprints. All 26 expected-success commands exited zero; all five intended
failures returned nonzero. The deterministic rerun was byte-identical. No RH `Main`
traversal, baseline-versus-candidate declaration difference, expression-node count,
serialized proof-size reduction, project-scale resource fit, or independent kernel
validation has been measured by this contribution.

## Contents

| File | Purpose |
|---|---|
| `ReachableDecls.lean` | Pinned declaration traversal, importing only Lean. |
| `compare_safe_fixtures.py` | Portable differential runner for the 12 safe fixtures. |
| `fixtures/ReachabilityFixtures.lean` | Small toy declarations and a metadata elaborator. |
| `fixtures/cases.json` | Exact roots and witnesses for each comparison. |
| `reference-export-targets.txt` | An unchanged copy of the RH frozen root list, with provenance below. |
| `safe12-fixture-report.json` | Completed receipt for these exact safe fixture and runner sources. |

Generated exports, compiled objects and logs belong in the selected output directory.
The runner writes `safe12-fixture-report.json`; the copy included here matches the four
source hashes recorded by that runner. It contains result hashes, not the generated exports.

## Run the safe fixtures

Use the exact official Lean 4.37.0-rc1 runtime above, including both `bin/lean` and
`bin/leanexport`. Python 3.10 or later is sufficient for the runner. From this repository's
root:

```sh
python3 audit/reachability-lean437/compare_safe_fixtures.py \
  --toolchain-dir /absolute/path/to/lean-4.37.0-rc1-linux \
  --output-dir /absolute/path/to/new-safe12-fixture-output \
  --timeout 180
```

The paths are placeholders. Each compiler or exporter command is printed before a
proceed/skip/abort prompt. Add `--yes` for an already authorized bounded batch run.
`--timeout` limits each small fixture command, not the whole suite. Set outer CPU and
memory limits appropriate to the machine running it.

The runner imports only the toy fixture module and the pinned Lean library. It sets
`LEAN_PATH` to the output directory and places the selected toolchain first on `PATH`.
An existing directory is reused only when its completed receipt, source and binary hashes,
and primary result artifacts match. An incomplete or mismatched directory is refused;
choose a fresh path to retry.

The comparisons use exact declaration-name components and kinds, expanding grouped
inductive exports into their individual types, constructors and recursors. The 12 cases
exercise:

- a theorem using a private proof, and an opaque value using a private definition;
- a dependency present only in a theorem's type;
- mutual and nested inductives, constructor roots and recursor roots;
- structure projections;
- natural-number and string literals;
- the special quotient package;
- metadata omitted or retained in the export, while a metadata-only name stays outside
  the declaration dependency graph.

The fixture definitions introduce no `axiom`, `sorry`, `admit`, or `unsafe` declaration.
The helper's optional unsafe-export mode is outside this suite's coverage. Fixture witness
checks require the projection, literal and metadata expression forms to survive compilation.
The runner also compares a deterministic rerun and checks rejection of missing roots,
empty roots, an unsupported option, and an existing output file. A successful complete run
contains 26 expected-success commands and five expected failures.

## Measure a built module

The helper's interface is:

```text
lean --run ReachableDecls.lean MODULE TARGETS_FILE NEW_NAMES_JSONL [--export-unsafe]
```

Use an exact, already built source revision and its pinned dependencies. Set `LEAN_PATH`
to those verified compiled outputs using the prepared environment for that checkout. With
the pinned `lean` executable on `PATH`, a frozen-root measurement has this form:

```sh
lean --run /absolute/path/to/audit/reachability-lean437/ReachableDecls.lean \
  Main /absolute/path/to/audit/reachability-lean437/reference-export-targets.txt \
  /absolute/path/to/new-result.names.jsonl \
  > /absolute/path/to/new-result.summary.json
```

`TARGETS_FILE` is nonempty and whitespace-separated, using the exporter's Lean name decoder.
It has no comment syntax, implicit roots or ignore-missing mode. The exact target text appears
in the summary. `NEW_NAMES_JSONL` must not already exist. A failed write may leave a partial
file; only exit status zero together with a valid summary is a completed measurement.

The JSON summary records the compiler identity, module, roots, total declaration count,
counts by kind and skipped unsafe names. The names file is deterministic: display names are
sorted with structural Lean-name comparison breaking ties, and each record includes its
string/numeric components so distinct names remain distinct.

For a before/after comparison, use the same frozen root bytes and toolchain, separately built
baseline and candidate revisions, and fresh output paths. Record the source revisions,
dependency pins, protected-input hashes and compiled-artifact provenance alongside the outputs.
Read-only inputs and an output-only writable directory keep the measurement separate from
the build. Importing a compiled artifact does not establish its source provenance.

The supplied root list is byte-identical to
[`export-targets.txt` at RH commit `307cef33f046955ee79dba47e0d828d06496d75f`](https://github.com/leanprover-community/riemann-hypothesis/blob/307cef33f046955ee79dba47e0d828d06496d75f/export-targets.txt).
Its Git blob is `e2d4c02bac8a1411eae85af0376c1aad3b6b5294`, and its SHA-256 is
`9eeb2e5e55be4a78f6e4983fc950dba915b45ad8aeb7a02a32341927a89e05e8`.
It includes the five final theorems and the explicitly listed primitive/axiom roots.

## Interpretation and reference semantics

The metric counts distinct exported constant identities. Types and constructor arguments can
retain a dependency even when a theorem never uses a particular projection. Alternative paths
can also keep a declaration reachable after one proof is removed. Generated private names need
careful interpretation when comparing name-set differences.

Declaration count does not measure proof-term length, mathematical minimality, exported bytes,
or expression nodes. A smaller proof can have an unchanged declaration closure. This helper
does not independently check the imported proofs or replace the source build, comparator,
axiom audit, or kernel replay.

The implementation follows these sources at the exact Lean pin:

- [LeanExport entry point](https://github.com/leanprover/lean4/blob/0b77e12952ad39077d80d8bd6b66d601f225c321/src/LeanExport.lean):
  target-name decoding and dynamic import behavior.
- [LeanExport.Basic](https://github.com/leanprover/lean4/blob/0b77e12952ad39077d80d8bd6b66d601f225c321/src/LeanExport/Basic.lean):
  declaration types and values, inductive/constructor/recursor expansion, quotient primitives
  and literal dependencies. Definition/theorem `all` metadata does not add dependency edges.
- [Lean.Environment](https://github.com/leanprover/lean4/blob/0b77e12952ad39077d80d8bd6b66d601f225c321/src/Lean/Environment.lean):
  private-data imports with imported extensions disabled (`loadExts := false`).
- [Expr.forEach](https://github.com/leanprover/lean4/blob/0b77e12952ad39077d80d8bd6b66d601f225c321/src/Lean/Util/ForEachExpr.lean):
  traversal of expression bodies; metadata payload names are not declaration dependencies.
- [ConstantInfo.isUnsafe](https://github.com/leanprover/lean4/blob/0b77e12952ad39077d80d8bd6b66d601f225c321/src/Lean/Declaration.lean):
  the exporter's classification of declarations skipped in the default mode.

Avoiding global serialization tables should reduce auxiliary allocation, but neither peak
memory nor completion time on the full RH project has been established. The 12 toy comparisons
can validate tested traversal behavior; they cannot establish project-scale performance or a
formal equivalence proof.
