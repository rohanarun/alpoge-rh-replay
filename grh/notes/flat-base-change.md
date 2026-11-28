# Flat base change in functor cohomology

This note explains `New.Variety.HasFlatBaseChange`: what it says, how the readable edition proves
it for the functors it needs, and where the p-adic comparison uses it. Everything here is in `Lib`;
names below omit the prefix `New.Variety.`.

## The statement

Cohomology in `Lib/Cohomology` and `Lib/PadicComparison` is Ext in a category of functors: for
functors `N` and `F` from a category `C` to abelian groups, `H N F n` is `Ext^n(N, F)`. Coefficients
often come as a functor `Φ` from `C` to `S`-modules; `moduleCoeff Φ` is the same functor viewed as
abelian groups, and `H N (moduleCoeff Φ) n` is an `S`-module.

For an `S`-algebra `T` and a `T`-module `M` (with `S → T → M` a scalar tower),
[`baseChangeMap`](../src/Lib/PadicComparison/Descent/TestCategory.lean#L194) is the `T`-linear map

    M ⊗_S H^n(N, Φ) → H^n(N, M ⊗_S Φ),    m ⊗ z ↦ (push of z along y ↦ m ⊗ y).

Here `M ⊗_S Φ` is `Φ` followed by `tensorWith T M`, the functor `X ↦ M ⊗_S X`.
[`HasFlatBaseChange N`](../src/Lib/PadicComparison/Descent/TestCategory.lean#L213) says that this
map is bijective for every degree `n`, every `Φ`, and every `S`, `T`, `M` with `M` flat over `S`.
It is a property of `N` alone: the coefficients and the flat module are quantified over.

## Representable functors: the Yoneda lemma

For an object `A`, let `ℤ[h_A]` be `freeAb (reprBy A)`, the free abelian group on the functor
represented by `A`.
[`HasBaseChange.baseChangeMap_bijective_freeAb_reprBy`](../src/Lib/General/Algebra/CohomologyBaseChange.lean#L134)
proves that the base change map is bijective for `N = ℤ[h_A]` in every degree, and it does not need
`M` to be flat:

- in degree 0 the Yoneda lemma identifies `H^0(ℤ[h_A], Φ)` with `Φ(A)`
  (`HasBaseChange.yonedaEquiv₀`), so both sides are `M ⊗_S Φ(A)`, and the base change map is this
  identification;
- in positive degree both sides vanish (the proof uses that they are subsingletons; the comment
  there notes that `ℤ[h_A]` is projective).

[`hasFlatBaseChange_freeAb_reprBy`](../src/Lib/General/Algebra/CohomologyBaseChange.lean#L154)
restates this as `HasFlatBaseChange (freeAb (reprBy A))`.

## Dévissage: long exact sequences

The step from representables to other functors goes through short exact sequences
`0 → X₁ → X₂ → X₃ → 0` of functors. Two notions from
[`BijectiveComparisons`](../src/Lib/Cohomology/Etale/BijectiveComparisons.lean#L419) organise it.

- `BijectiveUpTo f r`, for maps `f n`, is the first `r` of the conditions
  "`f 0` injective, `f 0` surjective, `f 1` injective, `f 1` surjective, …"
  ([`LongExactSequences`](../src/Lib/General/Algebra/LongExactSequences.lean#L145)).
- A family of maps `f N n`, indexed by functors `N` and degrees `n`, has
  [`Devissage`](../src/Lib/Cohomology/Etale/BijectiveComparisons.lean#L454) when it behaves like a
  map of contravariant δ-functors under the four and five lemmas. Along every short exact sequence,
  the first `r` conditions at `X₂` and the first `r − 1` at `X₁` give the first `r` at `X₃`
  (`StepwiseFourLemma`). And the functors on which `f` is bijective in all degrees form a closed
  class (`IsClosedClass`): the class contains every zero functor, and when it contains `X₁` it
  contains `X₂` exactly when it contains `X₃`.

[`HasBaseChange.devissage`](../src/Lib/General/Algebra/CohomologyBaseChange.lean#L195) shows that
for flat `M` the base change maps have `Devissage`. A short exact sequence `X` gives the long exact
sequence of `Ext(–, Φ)` (`LongExactSeq.contravariant`). Tensoring it with `M` gives
[`HasBaseChange.tensoredSeq`](../src/Lib/General/Algebra/CohomologyBaseChange.lean#L177), which is
again exact because `M` is flat (`Module.Flat.lTensor_exact`). The base change maps form a morphism
from `tensoredSeq` to the long exact sequence of `Ext(–, M ⊗_S Φ)`: each square commutes because the
base change map turns `M ⊗` (composition with a class) into composition with that class
(`HasBaseChange.baseChangeMap_lTensor_precompₗ`). The four and five lemmas for morphisms of long
exact sequences (`LongExactSeq.Hom.four_lemma`, `LongExactSeq.Hom.five_lemma`) then give the two
fields of `Devissage`. For a zero functor both sides of the base change map are subsingletons, so
that case is immediate.

## From representables to affinely covered functors

[`IsAffinelyCovered.devissage_bijective`](../src/Lib/PadicComparison/Descent/TestCovers.lean#L571)
is a general transfer. Let `ι` be a fully faithful functor from `C` to `A`-algebras with covering
points (`HasCoveringPoints`, in `Lib/General/Geometry/EtaleCharts`). Let `Y` be affinely covered:
it is separated and has one point `y` over some algebra `B` of which every point of every `Y(ι c)`
is an image. Then any family with `Devissage` that is bijective in all degrees at every
representable `ℤ[h_c]` is bijective in all degrees at `ℤ[Y ∘ ι]`. The proof is an induction on the
number `r` of conditions in `BijectiveUpTo`:

1. if `Y ∘ ι` has no points, `ℤ[Y ∘ ι]` is zero and the closed class contains it;
2. otherwise, a covering point gives a map from a representable functor onto `Y ∘ ι`;
3. the fibre powers of this cover are again affinely covered (`isAffinelyCovered_cech`), so the
   induction hypothesis applies to them with `r` conditions;
4. a Čech descent step (`cech_descent_step`) turns `r + 1` conditions on the cover and `r` on its
   fibre powers into `r + 1` conditions on the image, which is all of `Y ∘ ι`.

With the representable case above, this gives
[`IsAffinelyCovered.hasFlatBaseChange`](../src/Lib/PadicComparison/Descent/TestCovers.lean#L612):
`ℤ[Y ∘ ι]` has flat base change. The same file shows that functors with flat base change form a
closed class ([`HasFlatBaseChange.isClosedClass`](../src/Lib/PadicComparison/Descent/TestCovers.lean#L509)),
and that `ℤ[Y]` has flat base change when `Y` is isomorphic to the points of an `O_C`-algebra
([`hasFlatBaseChange_of_iso_reprBy`](../src/Lib/PadicComparison/Descent/TestCovers.lean#L619)).

## Transferring a comparison: the commutative square

What the p-adic comparison needs is not flat base change by itself, but its consequence for
comparison maps.
[`Comparison.IsBijective.baseChangeMap_bijective_iff`](../src/Lib/General/Algebra/CohomologyBaseChange.lean#L232)
considers a comparison `H^n(N, Φ) → H^n(N', Φ')` that is bijective in every degree, with `N` having
flat base change and `M` flat. The base change maps for `N` and for `N'`, the comparison tensored
with `M`, and the comparison for the coefficients `M ⊗ Φ`, `M ⊗ Φ'` form a commutative square
(`baseChangeMap_pull`). Two of its sides are bijective: the tensored comparison and the base change
map for `N`. So base change for `N'` holds in every degree exactly when the comparison stays
bijective after tensoring the coefficients with `M`.

## Where the comparison uses it

- **Period coefficients.**
  [`primitivePeriodMap_isBijective`](../src/Lib/PadicComparison/Primitive/Periods.lean#L239)
  assumes flat base change for `N` and `N'`. It first gets a bijective comparison with coefficients
  over `S` (`h_completion`, from
  [`HasFlatBaseChange.isBijective_of_isReductionMod`](../src/Lib/PadicComparison/Completion.lean#L423):
  bijective modulo `p` plus finiteness of the cohomology). Then
  `baseChangeMap_bijective_iff`, applied with the flat `S`-algebra `K`, moves this to coefficients
  tensored with `K` (`h_completion_tensor`, line 281).
- **The period map.** In
  [`exists_period_map`](../src/Lib/PadicComparison/HodgeTate/PeriodMap.lean#L175) the map `J` is
  the composite of an identification `E`, the base change map that moves `K` into the coefficients,
  and a pull-back along the primitive comparison. For proper charted `Y` all three factors are
  bijective. Flat base change appears twice: for the geometric points, as the first output of
  `finite_and_primitive_comparison`, and for the test points, as `h_pts` (line 246), from
  `IsAffinelyCovered.hasFlatBaseChange`.
- **Other users.** `HasFlatBaseChange` also appears in the crystalline comparison
  (`Lib/PadicComparison/Crystalline/ComparisonMap`), the perfect line
  (`Lib/Cohomology/ProjectiveLine/PerfectLine`), the toric tower (`Lib/PadicComparison/ToricTower`)
  and depth vanishing (`Lib/Cohomology/Hodge/DepthVanishing`); this note does not go through those
  uses.

## What the note does not claim

The representable case needs no flatness; flatness enters only through the exactness of
`tensoredSeq` in the dévissage step. `HasFlatBaseChange` is a statement about the Ext groups of
functor categories used in this edition. This note does not compare it with base change theorems
for étale cohomology in the literature.
