# Counting trivialised cocycles without local duality

This note explains the count in
[`New.IsLargeLevel.SplitPlaces.card_trivialised_of_isHigmanProjective`](../src/Lib/ClassField/GreenbergWiles/CocycleCounts.lean#L336).
It is the readable edition's substitute for the upper bound that the Greenberg–Wiles formula gives
when the dual Selmer group vanishes. In its place there are linear relations, given by power residue
symbols, among the values of a cocycle on tame inertia at auxiliary split primes; no Poitou–Tate or
local duality is used. Names below omit the prefix `New.`.

## The objects

Let `G` be the Galois group of `Ω` over a number field `K`, `U` an open normal subgroup and
`Δ = G ⧸ U`. Let `V` be a finite discrete `G`-module.

- **Trivialised cocycles**
  ([`DiscreteModule.trivialisedCocycles`](../src/Lib/ClassField/GreenbergWiles/SplitPrimeReciprocity.lean#L61)).
  These are pairs `(f, c)` with `f` a function on the places of `Ω` above `N` and infinity
  (`PlaceAboveLevel N`) and `c : G → V` continuous. They satisfy `g f(x) = f(g x) + c(g)`, and `c`
  vanishes on a set `I` of inertia elements. So `c` is a cocycle, with a trivialisation `f` at the
  places above `N` and infinity.
  [`HasFewCocycles k`](../src/Lib/ClassField/GreenbergWiles/SplitPrimeReciprocity.lean#L79)
  says there are between one and `#V ^ k` of them.
- **Split places**
  ([`IsLargeLevel.SplitPlaces`](../src/Lib/ClassField/GreenbergWiles/SelmerLevels.lean#L269)).
  These are finitely many primes `v i` of `K` (`i : ι`) prime to `N`, each with a place of `Ω` above
  it and a Frobenius element `s.φ i` in `U`. `I` is the union of the inertia groups above the
  primes not dividing `N` other than the `v i`.
- **Hypotheses on `V`.** The structure
  [`FiniteKilledFixedInj l U z n`](../src/Lib/General/Algebra/CartanMap.lean#L80) says that `V` is
  finite, killed by the prime `l` and fixed by `U`, and that `ρ(z) − n` is injective on it. Next,
  `V` is projective over `Δ` in Higman's sense
  ([`IsHigmanProjective`](../src/Lib/General/Algebra/CartanMap.lean#L63)): some additive
  `τ : V → V` has `∑_δ δ τ δ⁻¹ = 1`. Finally, `h_fix` is a condition on `l`-th roots of
  `N`-units: if `r ^ l` is a `U`-fixed `N`-unit and every `s.φ i` fixes `r`, then `U` fixes
  `z r / r ^ n`.

## The statement

Under these hypotheses:

- (a) `V.HasFewCocycles (PlaceAboveLevel N) I (#ι + 1)`, that is,
  `0 < #(trivialised cocycles) ≤ #V ^ (#ι + 1)`;
- (b) if moreover `z` acts on the `l`-th roots of unity by the power `n` and `K` is totally complex,
  there are exactly `#V ^ (#ι + 1)`.

## The two inputs

- **Reciprocity at the split places.**
  [`IsLargeLevel.SplitPlaces.power_residue_reciprocity`](../src/Lib/ClassField/GreenbergWiles/SplitPrimeReciprocity.lean#L906)
  takes elements `γ i` that generate tame inertia at the split places
  (`exists_isTameGeneratorFor`). It gives power residue symbols `b y i` of the `N`-units `y` of the
  field of `U` at the split primes, with three properties:
  - a trivialised cocycle that vanishes at all `γ i` vanishes on `U`;
  - for each `N`-unit `y`, the values `c(γ i)` satisfy one linear relation with coefficients
    `b (δ y) i`;
  - conversely, over a totally complex field, every family satisfying these relations comes from a
    trivialised cocycle.

  The docstring calls the last two clauses an explicit substitute for the Poitou–Tate duality
  behind the Greenberg–Wiles formula.
- **Units.**
  [`IsLargeLevel.dirichlet_fixedSUnits`](../src/Lib/ClassField/GreenbergWiles/SelmerLevels.lean#L593)
  is Dirichlet's theorem for `E`, the `N`-units of the field of `U`, with its `Δ`-action. `E` is
  finitely generated, and `E × ℤ` carries independent real linear forms, one for each `U`-orbit of
  places above `N` and infinity, which `Δ` permutes. Then
  [`card_hom_lattice_eq_card_equivariant`](../src/Lib/ClassField/GaloisCohomology/TateIndexFormula.lean#L270)
  uses the Higman trace `τ`. It shows that the `Δ`-maps `E × ℤ → V` that kill torsion are as many
  as the `Δ`-maps from the set of those orbits to `V`.

## The count

The proof sets up four additive maps (lines 377–404 of the file):

- `d : V → (G → V)`, the coboundary map `a ↦ (g ↦ g a − a)`;
- `j : (ι → V) × ker d → H`, where `H` is the `Δ`-maps `E × ℤ → V`. It sends `(a, c)` to
  `(y, k) ↦ ∑_{i, δ} b (δ y) i • δ⁻¹ (a i) + k • c`
  ([`symbolIntertwiningMap`](../src/Lib/ClassField/GreenbergWiles/CocycleCounts.lean#L166)).
  It is onto ([`mem_range_symbolIntertwiningMap`](../src/Lib/ClassField/GreenbergWiles/CocycleCounts.lean#L194)),
  by the Higman trace and `h_fix`;
- `r : trivialised cocycles → ker j`, `(f, c) ↦ ((c (γ i))_i, 0)`. Its values lie in `ker j` by
  the relations of reciprocity;
- `p : ker r → range d`, `(f, c) ↦ c`. On `ker r` the cocycle vanishes at the `γ i`, hence on `U`,
  so `f` descends to `U`-orbits. Averaging `f` along an orbit with `τ` gives `a` with `c = d a`.

Write `H₀ ≤ H` for the maps that kill torsion. Then:

- `#H₀ = #ker p`, by `card_hom_lattice_eq_card_equivariant`: `ker p` consists of the pairs `(f, 0)`
  with `f` equivariant on `U`-orbits;
- `p` is onto, since the constant function `a` trivialises the coboundary `d a`.

Two counts follow (`h_left`, `h_right`). The second is
[`AddMonoidHom.card_pow_succ_eq_card_mul_card_range_mul_card_ker`](../src/Lib/ClassField/GreenbergWiles/CocycleCounts.lean#L320),
applied with `j` onto:

    #(trivialised cocycles) = #H₀ · #range d · #range r,
    #V ^ (#ι + 1)           = #H  · #range d · #ker j.

Since `H₀ ≤ H` and `range r ≤ ker j`, this gives (a). For (b) both inclusions are equalities:

- every `x ∈ H` kills torsion, because `z` acts on a torsion element by `n` modulo `l`, so `ρ(z) − n`
  kills `x y`
  ([`torsion_le_ker_of_map_act_eq`](../src/Lib/ClassField/GreenbergWiles/CocycleCounts.lean#L252));
- `r` is onto by the converse half of reciprocity
  ([`exists_mem_trivialisedCocycles_of_mem_ker`](../src/Lib/ClassField/GreenbergWiles/CocycleCounts.lean#L275)),
  which needs `K` totally complex.

## Where it is used

- **Modules killed by `ℓ`, index prime to `ℓ`.** In
  [`exists_hasFewCocycles_torsion`](../src/Lib/ClassField/GreenbergWiles/RelationsModL.lean#L334)
  the module is the `ℓ`-torsion `M[ℓ]`, with `z = 1` and `n = 0`. Higman's criterion holds because
  the index of the subgroup is prime to `ℓ`
  ([`FiniteKilledFixedInj.isHigmanProjective_of_coprime`](../src/Lib/General/Algebra/CartanMap.lean#L141)).
  Only part (a) is used.
- **Modules with a central scalar.**
  [`hasFewCocycles_of_central`](../src/Lib/ClassField/GreenbergWiles/CocycleCounts.lean#L685)
  drops projectivity. `V` is killed by `l ^ r`, and some `z` with `l`-adic cyclotomic character `1`
  is central modulo `U`, with `ρ(z) − 1` injective. The comment at the head of its proof gives the
  route. Over a group normalising an `l`-Sylow subgroup, the count for modules killed by `l` is
  forced to its maximum. So cocycles lift along exact sequences,
  and by corestriction over the whole group. The count is then multiplicative, and `V` is filtered
  by modules killed by `l`.
- **The Greenberg–Wiles type bound.**
  [`exists_card_cocycles_le`](../src/Lib/ClassField/GreenbergWiles/Relations.lean#L584) applies
  `hasFewCocycles_of_central`. It is a case of the formula of Darmon–Diamond–Taylor, Theorem 2.19,
  in the form of a lower bound for the relations off a finite set of primes.

## What the note does not claim

These are the statements of the readable edition, read from its docstrings and proof comments. The
file cites Darmon–Diamond–Taylor, Theorems 2.18–2.19, and Wiles, Proposition 1.6, for the kind of
bound. This note does not check those references, and does not compare the hypotheses here with
the vanishing of a dual Selmer group.
