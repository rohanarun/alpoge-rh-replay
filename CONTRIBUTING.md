# Agent Instructions — Make PR #120 build

> **Priority right now:** help get [PR #120](https://github.com/leanprover-community/riemann-hypothesis/pull/120) to a clean build. It consolidates the Lean `v4.36.0` RH proof from ~149k to **47,881 modules (−67.9% files)**. The remaining work is a list of compile failures introduced by bundling. Each is small and self-contained. Do **not** claim legacy packets (`Claim P####` / `Claim M######`) or open 4.33 → 4.36 porting PRs here.

## Where the work is

- **Branch:** `rohanarun/riemann-hypothesis`, branch `opt/collapse-and-consolidate-4.36` (the head of PR #120).
- **Open failures:** [PR120-BUGS.md](PR120-BUGS.md). A 4-shard, 512-vCPU build updates it as new failures appear.
- **Before claiming:** [check the report against your checkout and live PRs](scripts/pr120-triage.md) with the read-only triage helper.
- Modules that fail only with `bad import` are **not** bugs. They import a broken module and will build once it's fixed. Fix the root failures in the list.

## How to take a bug

1. Check [open PRs against the branch](https://github.com/rohanarun/riemann-hypothesis/pulls) so you don't duplicate someone else's work.
2. Open a **draft PR early** against `rohanarun/riemann-hypothesis:opt/collapse-and-consolidate-4.36`, titled `Fix <Module>`. That's your claim.
3. One module (or one family, such as all `JetR` files) per PR.
4. **Claim before you start.** Every 15 minutes a coordinator script fixes unclaimed rows it can resolve mechanically (name collisions, and fixes that already exist on aliromman's branch), pushes them to the branch, and republishes [PR120-BUGS.md](PR120-BUGS.md). It never touches a file that an open PR against the branch modifies, and the list shows those rows as `claimed: #N @you`. Before you push, pull the branch so you're working on the latest fixes.
5. **Mark the PR "Ready for review" when your fix is done.** The coordinator cycle (every few minutes) merges ready PRs that only change `src/*.lean`, touch no protected files, add no `sorry`/`admit`/axioms/`unsafe`, and merge cleanly. A draft is also merged early if it passes the same checks, changes at most 5 files, and every file it changes is currently a failing row in [PR120-BUGS.md](PR120-BUGS.md), because it can't make things worse. Merged PRs are closed automatically. If two PRs fix the same file, the first to merge wins; rebase the other if it still adds something.

## How to diagnose

Most failures come from bundling: several original files were merged into one `BundleNNNN.lean` (each section is marked `-- bundled from <OriginalModule>`), and their `open`s now see each other's names.

- **Ambiguous term / wrong declaration picked.** Look up the original module on `main` (`c779160312`): `git grep -F '<the failing line>' c779160312 -- src`. Its `open`s and imports tell you which declaration was meant. Qualify the bare name to that declaration's full name, **only inside that original's `namespace … end` block**. Never rewrite the `def`/`theorem` line that declares the name.
- **Lean looks up enclosing namespaces before opened ones.** Inside `namespace PI.Foo`, a bare `sigR` finds `PI.sigR` before an opened `GenusMassVolumes.sigR`. `open X hiding y` does **not** help there; qualify instead.
- **Unknown identifier / already declared.** Usually a declaration lost or duplicated when thin wrappers were collapsed. Check aliromman's [`codex/pr120-integration-4.36`](https://github.com/aliromman/riemann-hypothesis/tree/codex/pr120-integration-4.36) branch first; it fixes many of these.
- **Instances (`failed to synthesize`, `instance problem is stuck`).** Supply the instance or measure explicitly. See `DivisorProofs/Bundle0386`/`Bundle0408` on the branch for an example.

## Strict rules

- **Never modify** `src/Challenge.lean`, `src/Statements.lean`, or `comparator.json`.
- **Never introduce** `sorry`, `admit`, new `axiom`s, or unsafe features. Don't change what a theorem states.
- Build the module you changed if you can (`lake build <Module>`; `lake exe mathlib/cache get` for Mathlib). If you can't build locally, say so in the PR; the coordinator's 4-shard build will check it.
- In the PR, paste the original error and explain where the fix came from (which original module or declaration).

---

*Historical Lean 4.33.1 replay documentation is preserved in git history and [STATUS.md](STATUS.md).*
