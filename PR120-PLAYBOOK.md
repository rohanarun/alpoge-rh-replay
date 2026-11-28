# PR #120 fix playbook

How to fix the remaining compile failures on the consolidated Lean 4.36 branch
(`rohanarun/riemann-hypothesis:opt/collapse-and-consolidate-4.36`, upstream
[leanprover-community/riemann-hypothesis#120](https://github.com/leanprover-community/riemann-hypothesis/pull/120)).
Open failures are listed in [PR120-BUGS.md](PR120-BUGS.md). This playbook collects every failure pattern found
so far and the fix that worked. Almost every open row matches one of them.

## Background: why things break

Small modules were merged into "bundle" files. Each section of a bundle is marked `-- bundled from <OriginalModule>`.
A bundle imports the **union** of its members' imports, so each original proof now sees declarations and instances
it never saw before. The proofs were correct on the original tree (`main` at `c779160312`). Your job is to restore
the original meaning, never to change it.

## Workflow

1. Pick an unclaimed row in [PR120-BUGS.md](PR120-BUGS.md) and open a draft PR titled `Fix <Module>` against
   `opt/collapse-and-consolidate-4.36` to claim it. Add fix commits on top; force-pushing is fine too.
2. Find the original module: it's named in the `-- bundled from` marker above the failing line, or is the file's own path.
   Read it on `main` at `c779160312`. Its `import` lines decide which of two same-named declarations the author meant.
3. Build only the module you changed and its importers: `lake build <Module>`. The whole tree is not green yet.
   Run `lake exe mathlib/cache get` first.
4. Mark the PR ready. The coordinator auto-merges PRs that change only `src/**/*.lean`, touch no protected file
   and add no `sorry`/`admit`/`axiom`/`unsafe`/`implemented_by`/`native_decide`.

To compare the work needed on a cold checkout, run `python3 scripts/module-build-scope.py --repo ../riemann-hypothesis MODULE [MODULE ...]` from the replay checkout with Python 3.9+ and Lean 4.36.0 installed. Use a complete proof source tree. The tool counts each target and its distinct transitive imports under `src/`, including local edits. Add `--list-importers` to find the direct importers to test after a fix. Mathlib, local cache state and individual elaboration times affect the actual build cost. Compile the selected target to check the reported error.

**Hard rules:** never change a theorem statement's meaning. Never edit `Challenge.lean`, `Statements.lean`,
`comparator.json`, `lakefile*` or `lean-toolchain`. Never rename or qualify a name on its own declaring line;
qualify uses only. Prefer qualifying a use over adding `open`.

## Pattern 1 — namespace-prefix shadowing (most common)

Inside `namespace A.B.C`, a declaration in that namespace or a parent (`A.B.foo`) silently beats an `open`ed
namespace's `foo`, even `open X (foo)`. **Symptoms:** type mismatches, "Function expected", "Invalid field",
"Invalid argument name", a `rw` that can't find a pattern where the target shows `X.foo` but the pattern shows `foo`,
even `whnf`/`isDefEq` heartbeat timeouts. **Fix:** qualify the use to the namespace the original saw.

Known cases:
- **Heights family** (`GroundTheory.Heights₂.Heights.*`): `HermLine`, `fibre`, `MRing`, `MRingOver`, `IsRelevant`,
  `IsMultiHomog` resolve to the Heights₂ versions, which take `ℕ`. The multi-projective ones (index `ι : K → Type`) are
  `ReciprocityTheory.ChartRestriction.G.Geo.X`; `linForm` and `fibreIdeal` are `ReciprocityTheory.ChartRestriction.G.AI.I4.X`;
  `unitDeg` is `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg`; `isMultiHomog_{add,mul,one,zero}` are
  `GroundTheory.Heights₂.Heights.LowerBoundFree.*`.
- **`embT`** inside `Formalism.L2.*` now means `Formalism.L2.embT`; originals meant `Formalism.L2.Forms.embT`,
  `Formalism.MainNotions.TaylorLogMetric.embT`, or (KernelLattices) `Formalism.L2.Ker.Cd.TaylorLogMetric.embT`.
  Already-built dependencies may use either; `erw`, `show …` or a trailing `rfl` bridges the definitional equality.
- **Inside `PI.*`:** `PI.sigR` shadows `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR`; `PI.bc` shadows
  `Formalism.UG.bc`; `hform` should be `Formalism.UG.hform`; `latA` is `PI.OmLocU.latA` vs `PI.VolStabSW.SdDualW.latA`;
  `unrealify`/`realifyFun` should be `Formalism.MainNotions.S.*`.
- **Inside `GlobalTheory.*`:** `dualLattice` resolves to `GlobalTheory.dualLattice` instead of
  `GroundTheory.Heights₂.Heights.dualLattice`; `IsNormalScheme` resolves to the class `GlobalTheory.IsNormalScheme`
  instead of `ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme`.
- **Inside `Formalism.MainNotions.G.*`:** the project's `rank_le` shadows Mathlib's, so use `_root_.rank_le`.
- A doubled qualification like `X.Y.X.Y.foo` is a bad earlier automated edit. Reduce it to `X.Y.foo`.

## Pattern 2 — ambiguous names

| Name(s) | Candidates | Usually meant |
|---|---|---|
| `Dec` | `ReciprocityTheory.Gal.Dec`, `Neutral.B1.Dec` | check the closure |
| `HChar`, `OverP`, `PiBar`, `Omg`, `IsUnitAt`, `IsUnifAt`, `IsChiPsi`, `upF`, `exists_unif`, `atFin`, `unif` | `GlobalTheory.Mem.Chr.*`, `Formalism.L2.Host.*` | `Formalism.L2.Host` |
| `Ideles`, `diagUnits`, `localIdele` | `GlobalTheory.Mem.Chr.*`, `Neutral.B1.*` | `Neutral.B1` |
| `locF` | `GlobalTheory.Mem.Chr.locF`, `Neutral.B1.locF` | check the closure |
| `Unf`, `toC`, `gxSnd`, `relab`, `rdU`, `spMap_comp'`, `epsMul_comp_alg` | `Formalism.L2.PjFree.*`, `Formalism.L2.Pj.*` | `PjFree` when the original imported the Free variant |
| `dInv` | `GlobalTheory.SgGlob.dInv` | |
| `latK` | `Formalism.MainNotions.G.KAat.latK`, `Formalism.L2.Col.latK` | check the closure |
| `IsConn` | `GlobalTheory.PDivLat.IsConn` | |
| `ev_C` | `Formalism.L2.FormalSeriesBounds.PartialDerivEval.ev_C`, `…Geo.Tor.Germ.ev_C` | `PartialDerivEval` |
| `finitePart` | `GlobalTheory.EllipticCM.finitePart` | |
| `borel` | Mathlib `_root_.borel`, `GroundTheory.Automorphic.borel` | Mathlib, where the original used it |

`GlobalTheory.Mem.Chr` duplicates most of `Formalism.L2.Host` and part of `Neutral.B1`. Decide each name by the
original module's import closure, not by guessing.

## Pattern 3 — instance-search timeouts

Symptom: `failed to synthesize … (deterministic) timeout at typeclass`. Culprits found so far:

| Culprit instance | What it breaks |
|---|---|
| `UpperTheory.V.Pr.IsCD.toIsDomain`, `UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing` | every `IsLocalRing`/`IsDomain` search (dangling parameter `O`) |
| `UpperTheory.V.Alg.IsCO.toIsLocalRing` | same shape |
| `Formalism.BasicNotions.Examples₂.instIsEmptyClsEmptyColumnChain` | `IsEmpty Empty`, `Unique (Ix Empty)` |
| `GlobalTheory.LGrp.locallyCompact_GL`, `GlobalTheory.SplitFlip.locallyCompact_GL`, `GlobalTheory.SplitFlip.secondCountable_GL` | `LocallyCompactSpace`/`SecondCountableTopology (GL _ R)` on adele rings |
| `GroundTheory.PAdicHodge.subfield_valuativeRel` | conflicts with `GroundTheory.LocalField.intermediateField_valuativeRel` |

**Fix:** put `attribute [-instance] X Y in` directly before the failing declaration. A file-level `attribute
[-instance]` inside a `section … end` stops at `end`. An alternative is an explicit
`haveI : IsLocalRing R := UpperTheory.V.Alg.IsCO.toIsLocalRing O`. To find an unknown culprit, test
`set_option trace.Meta.synthInstance true in example … := inferInstance`; the instance whose subtree dominates the
trace is the culprit. As a last resort, use `set_option synthInstance.maxHeartbeats 400000 in` on one declaration,
and only if it then compiles quickly.

## Pattern 4 — other Lean 4.36 / elaboration changes

- **Quotient-group instances** (`(H).Normal`, `Mul (G ⧸ H)`, `CommGroup (Ideles K ⧸ …)`) fail because the nested
  search exceeds the default `maxSynthPendingDepth 1`. Fix: `set_option maxSynthPendingDepth 2 in` on the declaration.
- **Instance diamonds on Subalgebra/IntermediateField carriers** cause `whnf` timeouts (for example `↥(ptRing …)` over `c.F`).
  Pin the local instances right after the `let`: `letI : CommRing A := inferInstance`, `letI : Algebra K A := inferInstance`.
- **`rw` with a def's equation lemmas fails:** use `rw [show x = y from rfl]`, `erw`, or `simp <;> rfl`.
- **`MonoidHom.instCommGroup` not found by search:** elaborate it explicitly with `letI`.
- **Duplicate same-named theorems that differ only in binder explicitness:** call them with named arguments.
- **`unfold … Matrix.mulVec`** fails on 4.36: use `delta Matrix.mulVec dotProduct`.

## Recently found (Nov 23, afternoon)

- **`GlobalTheory.AdmLoc.modFun`** is a high-priority `Module` instance that derails `Module`/`Decidable` searches.
  Fix: `attribute [-instance] GlobalTheory.AdmLoc.modFun in` before the declaration.
- **`GlobalTheory.entries`** shadows `Formalism.BasicNotions.entries` inside `GlobalTheory.*`: qualify the use.
- **Ideal powers** now go through `Submodule.instPowNat`, so `pow_mul`/`pow_two` on ideals need `(M := Ideal R)`.
- **`Pi.single a 1`** can default to `ℕ`: give the codomain explicitly (for example `(C := TrivSqZeroExt …)`).
- **Slow searches on `Ob l` (`PreTilt`):** a generic lemma like `map_neg` routes through `Module ℚ≥0` and times out.
  Use the bundled hom's own lemma instead (`A.s.map_neg`).
- **`cj_cj`** should be `LevelTowerAlt.Charts.cj_cj`. **`dualMap`** in GeometryProofs may need `_root_.` before
  `GlobalTheory.CompanionTheory.Ar.dualMap`.
- **`smul_smul`/`mul_smul` never match on `KaehlerDifferential` (Ω[S⁄R]).** Quotient-ring scalars use a derived
  `SMul` (`instSMulKaehlerDifferentialOfSMulCommClass`) that doesn't unify with `MulAction.toSMul`, because
  `KaehlerDifferential` is a plain `def`. Rewrite with `← smul_assoc, smul_eq_mul`, which goes through `IsScalarTower`.
- **Tensor-product instances** such as `AddCommGroup ((⨂ …) ⊗[ℂ] (⨂ …))` need `set_option maxSynthPendingDepth 2 in`
  (no culprit instance, just Lean 4.36's lower default); pass the space explicitly to `invFun` with `(V := …)`.
- **`GlobalTheory.AdmLoc.modFun`** also breaks `map_sub` on linear maps into `κ → OB l O`; same `[-instance] … in` fix.
- **"failed to read file … .olean"** on a machine with all dependencies built is not a Lean error. The kernel limit
  `vm.max_map_count` is too low; Lean needs at least `1048576` (`sudo sysctl -w vm.max_map_count=1048576`).

## If nothing works

If a section is identical to the original and still fails only because of the bundle's widened imports, the reliable
fallback is to split that section back into its own file with the original's imports. Then make the bundle import that
file. Say so in the PR so the coordinator can review the extra file.

## Root causes from the late layers (for the 4.37 regeneration)
- [Dharmavati213's consolidated list of root causes behind 55 late-layer failures](https://github.com/rohanarun/alpoge-rh-replay/issues/35028), mostly leaked instances from widened imports (disable in the section, or lower priority at the source). Reuse it as a checklist when the consolidation is regenerated on `main`.
- `attribute [-instance]` lines are double-edged: several files broke when a mass edit added or removed them (`ExistsIsHaarProbabilityMaxCompactHermitian`, `ReBaseZeta`, `HodgeTateFromSandwich`). Always check a change against **current** dependencies, never a stale build tree.
- Independent full builds: roy7 (green at `b35a3239c4`, 114,030 jobs, 0 errors), maugomez77 (iterative ~20-min full builds with warm artifacts).
