module

public import Lib.Cohomology.ProjectiveLine.FibrewiseBasis
public import Lib.Cohomology.ProjectiveLine.TiltedTheory

/-!
# Leray–Hirsch bases and the projective line formula for the tilted theory

The first part works over the tests `New.Variety.TestOver A` with coefficients killed by `ℓ`. Here
`A` is an absolutely integrally closed local domain in which the prime `ℓ` is invertible (the
instance `New.Variety.InvertsPrime A ℓ`). The projective line formula
(`New.Variety.TorsionCoeff.HasLineFormula`) says that the classes 1 and η identify Ext(S,
F) ⊕ Ext(S, F) with Ext(S, F) taken over the category of points of ℙ¹; here η is
`New.Variety.TorsionCoeff.cupClass`, the product with `New.Variety.etaClass` at the tautological
point of ℙ¹.

## Main definitions and results

* `New.Variety.isLerayHirschBasis_of_forall_isField`: bijectivity passes from the fields under a
  test to the test, given `New.Variety.IsDetectedAtPoints` (zero sets of classes are open;
  invariance under field extension).
* `New.Variety.exists_isLerayHirschBasis_of_isCohomDense`: a basis exists on the special fibre
  `New.Variety.IdealFamily.ofMaximalIdeal`.
* `New.Variety.isDetectedAtPoints_projLine`: the locally constant `ℤ/ℓ`-valued functions on pairs
  (test over `A`, point of ℙ¹) satisfy `New.Variety.IsDetectedAtPoints`.
* `New.Variety.exists_isTodaCancellation`: from a square `δ' ≫ i = i ≫ δ` with `i` a monomorphism,
  the product η of the classes of two short exact sequences is cancelled
  (`New.Variety.IsTodaCancellation`): after an exact functor that makes the cokernel of `i` acyclic,
  the product with a class ω is onto, and the pull-back of η m along `j` determines the pull-back of
  m along `ε`.
* `New.Variety.isLerayHirschBasis_lineBasis_of_injective`: two conditions on the product with η that
  give the formula at S.
* `New.Variety.hasLineFormula_tiltTheory`: the formula, from the cover of the perfect ℙ¹ by two
  discs.

Notions from other files:
* `New.Variety.TestOver`: The category of tests over A: the full subcategory of commutative
  A-algebras whose underlying rings are test rings.
* `New.Variety.lerayHirsch`: For classes θ_i in Ext^{d_i}(ΦG, F), the Leray–Hirsch map w ↦ Σ
  θ_i∘Φ(w_i) from finitely supported families in total Ext(S, G) to total Ext(ΦS, F);
  `New.Variety.IsLerayHirschBasis` says that it is bijective.
* `New.Variety.H`: The group Ext^n(N,F) in the category of functors from C to abelian groups.
* `New.Variety.projLine`: The projective line as a functor on rings: B goes to the set of points
  (1 + uv : v) with u, v in B, that is, pairs (u, v) modulo `New.Variety.projLineSetoid`.
* `New.Variety.freeAb`: The functor sending a set-valued functor Y to ℤ[Y], whose value at A is the
  free abelian group on Y(A).

## Relation to the literature

Known result: Künneth formula over a field for mod-ℓ étale cohomology, in Leray–Hirsch form. It is
proved here only over the special fibre of an absolutely integrally closed local domain. It states
that a basis of the cohomology over the residue field that contains a given non-zero class stays a
basis over every test ring of the special fibre. Source: SGA 4 XVII 5.4.3; Milne, Étale Cohomology
VI.8.

See also `Lib.Cohomology.ProjectiveLine.ConstantLineFormula`.
-/
