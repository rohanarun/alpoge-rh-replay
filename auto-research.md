# Agent Instructions — Make PR #120 build

> **Priority right now:** help get [PR #120](https://github.com/leanprover-community/riemann-hypothesis/pull/120) to a clean build. It consolidates the Lean `v4.36.0` RH proof from ~149k to **47,884 modules (−67.9% files)**. The remaining work is a list of compile failures introduced by bundling. Each is small and self-contained. Do **not** claim legacy packets (`Claim P####` / `Claim M######`) or open 4.33 → 4.36 porting PRs here.

> **Build status:** see [PR120-BUGS.md](PR120-BUGS.md) for the latest published counts and root failures. The **Open** table lists failures from the normal build. When the **Look-ahead** table is present, it lists failures from a scratch build that can check later modules. Prefer unclaimed round 2+ rows when available.

## Read these first

1. **[PR120-BUGS.md](PR120-BUGS.md):** the periodically refreshed list of root failures from the four build shards. Rows marked `claimed: #N @you` are taken.
2. **[PR120-PLAYBOOK.md](PR120-PLAYBOOK.md):** every failure pattern found so far, with the fix that worked. **Most open rows match one of its patterns**: namespace-prefix shadowing, a table of ambiguous-name pairs, instance-search culprits such as the `IsCD`/`IsCO` instances, and Lean 4.36 elaboration changes such as `maxSynthPendingDepth`.

## Where the work is

- **Branch:** `rohanarun/riemann-hypothesis`, branch `opt/collapse-and-consolidate-4.36` (the head of PR #120).
- Modules that fail only with `bad import` are **not** bugs. They import a broken module and will build once it's fixed. Fix the root failures in the list.
- The whole tree is not green yet, so `lake build` of everything (or `lake comparator`) can't pass. Verify your fix by building the module you changed and its importers.

## How to take a bug

1. Pull the latest branch and check [open PRs against it](https://github.com/rohanarun/riemann-hypothesis/pulls). Compare the reported diagnostic with the current source and check the file's recent commits with `git log -p -- src/<path>.lean`. A diagnostic can outlive its fix even when the file is unchanged since the report's listed head. For example, the Open table still listed the invalid `open` in `ChartDensityIntegrable` at `7e4ed7d840`, which already contained [the fix in #790](https://github.com/rohanarun/riemann-hypothesis/pull/790). Reproduce the error with a module build when possible.
2. Open a **draft PR early** against `rohanarun/riemann-hypothesis:opt/collapse-and-consolidate-4.36`, titled `Fix <Module>`. That's your claim.
3. One module (or one family, such as all `JetR` files) per PR.
4. **Claim before you start.** Every ~15 minutes a coordinator script fixes unclaimed rows it can resolve mechanically (name collisions), pushes them to the branch, and republishes [PR120-BUGS.md](PR120-BUGS.md). It never touches a file that an open PR against the branch modifies. Before you push, pull the branch so you're working on the latest fixes.
5. **Mark the PR "Ready for review" when your fix is done.** Every 15 minutes the coordinator merges ready PRs that only change `src/*.lean`, touch no protected files, add no `sorry`/`admit`/axioms/`unsafe`, and merge cleanly. A draft is also merged early if it passes the same checks, changes at most 5 files, and every file it changes is currently a failing row in [PR120-BUGS.md](PR120-BUGS.md). Merged PRs are closed automatically. If two PRs fix the same file, the first to merge wins. If your PR is closed as superseded, the file was already fixed another way; pick a new row.
6. **Force-pushing and rebasing are fine.** The coordinator now fetches PR heads with a forcing refspec, and handles non-ASCII paths such as `GaloisCohomology₂/`. If a PR of yours was stuck on `fetch failed` or `empty diff` before Nov 23, that was a coordinator bug; it's fixed now.

## How to diagnose

Most failures come from bundling. Several original files were merged into one `BundleNNNN.lean` (each section marked `-- bundled from <OriginalModule>`), and each original proof now sees the imports, names and instances of its neighbours.

- **Find the original.** Look it up on `main` (`c779160312`): `git grep -F '<the failing line>' c779160312 -- src`. Its `open`s and imports tell you which declaration was meant. Qualify the bare name to that declaration's full name, **only inside that original's `namespace … end` block**. Never rewrite the `def`/`theorem` line that declares the name.
- **Lean looks up enclosing namespaces before opened ones.** Inside `namespace PI.Foo`, a bare `sigR` finds `PI.sigR` before an opened `GenusMassVolumes.sigR`. `open X hiding y` does **not** help there; qualify instead. The playbook lists the known cases.
- **Instance timeouts (`failed to synthesize … timeout at typeclass`).** Usually a newly visible instance derails the search. Check the culprit table in the playbook first; the usual fix is `attribute [-instance] <culprit> in` placed right before the failing declaration.
- **Unknown identifier / already declared.** Usually a declaration lost or duplicated when thin wrappers were collapsed. Compare with the original module on `main`.
- **Last resort:** if a section is identical to the original and still fails only because of the bundle's widened imports, split it back into its own file with the original's imports, and say so in the PR.

## Strict rules

- **Never modify** `src/Challenge.lean`, `src/Statements.lean`, `comparator.json`, `lakefile*` or `lean-toolchain`.
- **Never introduce** `sorry`, `admit`, new `axiom`s, `native_decide`, `implemented_by` or unsafe features. Don't change what a theorem states.
- Build the module you changed if you can (`lake build <Module>`; `lake exe mathlib/cache get` for Mathlib). If you can't build locally, say so in the PR; the coordinator's 4-shard build will check it.
- In the PR, paste the original error and explain where the fix came from (which original module or declaration).
