module

import TauCeti.Algebra.Group.AddChar.Basic
public import Mathlib.Algebra.GroupWithZero.Torsion
public import Mathlib.CategoryTheory.Countable
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import TauCeti.MeasureTheory.Integral.Pi
public import Lib.DiscreteSeries.Bruhat.FloorGroups
public import Lib.General.Measure.IntegralOperators
public import Lib.General.Measure.QuadricDisintegration

/-!
# Heisenberg elements, measures of the floors, hyperbolic bases and Plancherel at a place

Algebra and measure theory on the unitary group `G` of the form `New.Shape.Form.splitGram T`, first
over a ring with involution and a `τ` of trace one, then over a place `A` (`New.Floors.Place`),
along its floors. The basis is `e_a`, a middle block, `e*_a` (`a < ϱ`). `V_l` is spanned by the
basis vectors of floor at least `l`: for `l ≤ ϱ`, the middle block and the pairs with `l ≤ a`. `h`
is the form. The frame `f_0, …, f_ϱ` (`New.Shape.besselFrame`) is `e_0, …, e_(ϱ-1)` followed by
the last vector `z` of the middle block.

In `New.Floors.FloorGroups`, the groups `floorGroup`, `unipotentBelow`, `floorUnipotent` and
`partialUnitriangularGroup` are `G_l = U(V_l)`, `N_(<l)`, `N_l = G_l ∩ N_(<l+1)` and `Q_l`. The
group `Q_l` consists of the elements unitriangular on the first `l` frame vectors, for `l ≤ ϱ + 1`.

`∗ₘ` is convolution of measures, so `μ ∗ₘ dirac s` is the right translate of `μ` by `s`.

* `New.Floors.TraceOne.heisenbergElem`, `New.Floors.FloorGroups.exists_eq_heisenbergElem_of_mem`:
  `N_a` is a Heisenberg group, given by Eichler maps.
* `New.Floors.FloorGroups.bijOn_mulVec_eStar`: `u ↦ u e*_a` maps `N_a` bijectively onto the
  isotropic vectors `y` of `V_a` with `h(e_a, y) = 1`.
* `New.Floors.FloorGroups.existsUnique_prod_of_mem_besselU`: an element of `N_(<ϱ)` is a product in
  `N_0 ⋯ N_(ϱ-1)` with unique factors.
* `New.Floors.Place.heisenbergMeasure`, `New.Floors.ascConv`: invariant measures on `N_l` and, by
  convolution, on `N_(<j)`.
* `New.Floors.HyperbolicBasis`, `New.Floors.HyperbolicBasis.floorQuadricMeasure`: hyperbolic bases
  of `V_ϱ` and `V_b`, and measures on quadrics in `V_b`, which disintegrate the Haar measure
  (`New.Floors.HyperbolicBasis.isDisintegration_floorVolume`).
* `New.Floors.Place.plancherel_inequality`: Plancherel's inequality on `A ^ ι`.

Notions from other files:
* `New.SplitIndex`: The index set made of ϱ indices, a middle set μ, and ϱ further indices, as a
  disjoint union.
* `New.Shape.Form.splitGram`: The Gram matrix of ϱ hyperbolic planes and a middle space with Gram
  matrix T: identity blocks pair the first and last ϱ indices, T is the middle block, all else is
  zero.
* `New.Floors.FloorGroups.floorOf`: The floor of a basis index: `a` for `e_a` and `e*_a`, `ϱ` for
  `z`, `ϱ + 1` for the other middle indices.
* `New.inclMatrix`: For a map u: m → n of index sets, the n×m matrix whose j-th column is the
  standard basis vector e_{u(j)}.

## Relation to the literature

Known; see `Lib.DiscreteSeries.Bruhat.ComplexPlace` for sources.
-/

@[expose] public section

noncomputable section

namespace New.Floors

open Matrix MeasureTheory Measure Sum Function ENNReal Fintype FloorGroups Filter TraceOne Place U
  Subgroup

variable {A : Type} [CommRing A] [StarRing A] {𝔰 : Shape} {l : ℕ}

namespace FloorGroups

variable [TraceOne A] {T : 𝔰.Form A} (a : Fin 𝔰.ϱ)
  {g s : T.G} [H : IsHermitianUnit T.splitGram]
  (p q : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) × skewAdjoint A)

/-! ### The Heisenberg groups of the floors and the Bessel subgroup -/

omit [StarRing A] [TraceOne A] T H in
private lemma inclMatrix_floor_apply_eq_zero (v : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A)
    {i : 𝔰.BesselIndex} (hi : floorOf i ≤ a) :
    (inclMatrix A (↑) *ᵥ v) i = 0 :=
  (inclMatrix_val_mulVec v i).trans (dite_eq_right (by lia))

omit [TraceOne A] H in
private lemma inclMatrix_floor_pair_single_eq_zero (v : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A)
    {j : 𝔰.BesselIndex} (hj : floorOf j ≤ a) :
    star (inclMatrix A (↑) *ᵥ v) ⬝ᵥ T.splitGram *ᵥ Pi.single j 1 = 0 := by
  rw [dotProduct_mulVec, dotProduct_single, mul_one,
    vecMul_splitGram_apply j (hj.trans_lt a.is_lt), Pi.star_apply,
    inclMatrix_floor_apply_eq_zero a v (by rw [floorOf_oppositeIndex]; exact hj), star_zero]

private lemma heisenbergElem_mem_unitary :
    let v := inclMatrix A (↑) *ᵥ p.1
    let M := eichlerMap T.splitGram (Pi.single (inl a) 1) (-v)
      (element * star v ⬝ᵥ T.splitGram *ᵥ v - p.2)
    Mᴴ * T.splitGram * M = T.splitGram := by
  intro v M
  -- The Eichler map is unitary: `e_a` is isotropic and orthogonal to `v`, and the parameter has
  -- trace `h(v, v)` because `τ + star τ = 1` and `p.2` is skew.
  have h_trace : element * star v ⬝ᵥ T.splitGram *ᵥ v - p.2 +
      star (element * star v ⬝ᵥ T.splitGram *ᵥ v - (p.2 : A)) =
        star (-v) ⬝ᵥ T.splitGram *ᵥ (-v) := by
    have h_herm : star (star v ⬝ᵥ T.splitGram *ᵥ v) = star v ⬝ᵥ T.splitGram *ᵥ v :=
      star_dotProduct_mulVec_comm H.conjTranspose_eq v v
    rw [star_sub, star_mul, h_herm, p.2.2, sub_neg_eq_add, star_neg, mulVec_neg,
      neg_dotProduct, dotProduct_neg, neg_neg]
    rw [show star (element : A) = 1 - element from eq_sub_of_add_eq' (element_add_star (A := A))]
    ring
  have h_iso : star (Pi.single (inl a) (1 : A)) ⬝ᵥ T.splitGram *ᵥ Pi.single (inl a) 1 = 0 := by
    rw [Pi.star_single, star_one, single_dotProduct, one_mul,
      splitGram_mulVec_apply (inl a) a.is_lt]
    exact Pi.single_eq_of_ne (by simp) _
  have h_orth : star (-v) ⬝ᵥ T.splitGram *ᵥ Pi.single (inl a) 1 = 0 := by
    rw [star_neg, neg_dotProduct, neg_eq_zero]
    exact inclMatrix_floor_pair_single_eq_zero a p.1 le_rfl
  obtain ⟨e, he⟩ := exists_unitary_eq_eichlerMap (x := Pi.single (inl a) 1) H.conjTranspose_eq
    h_iso h_orth h_trace
  dsimp only [M]
  rw [← he]
  exact mem_unitaryGroupOf_iff.1 e.property

/-- The isometry ν(v, β) of floor a: the Eichler transformation with
e*_a ↦ e*_a + v + (β − τh(v,v))e_a, for β skew. Here v is a vector of the floors at least a + 1,
extended by zero. -/
def _root_.New.Floors.TraceOne.heisenbergElem : U T.splitGram :=
  let v := inclMatrix A (↑) *ᵥ p.1
  U.of H.isUnit
      (eichlerMap T.splitGram (Pi.single (inl a) 1) (-v)
        (element * star v ⬝ᵥ T.splitGram *ᵥ v - p.2)) <| by
    exact heisenbergElem_mem_unitary a p

/-- The Heisenberg element ν(v, β) sends w to w + w(e*_a)v + ((β − τh(v, v))w(e*_a) − h(v, w))e_a.
Here w(e*_a) is the e*_a coordinate of w, and v is the vector of floors at least a + 1, extended by
zero. -/
@[local simp↓]
lemma heisenbergElem_mulVec (w : SplitIndex 𝔰.ϱ 𝔰.MiddleIndex → A) :
    let v := inclMatrix A (↑) *ᵥ p.1
    heisenbergElem (T := T) a p *ᵥ w =
      w + w (eStar a) • v +
        ((p.2 - element * star v ⬝ᵥ T.splitGram *ᵥ v) * w (eStar a) - star v ⬝ᵥ T.splitGram *ᵥ w) •
          Pi.single (inl a) 1 := by
  have h_coe : (heisenbergElem (T := T) a p).val.val =
      eichlerMap T.splitGram (Pi.single (inl a) 1) (-(inclMatrix A (↑) *ᵥ p.1))
        (element * star (inclMatrix A (↑) *ᵥ p.1) ⬝ᵥ T.splitGram *ᵥ inclMatrix A (↑) *ᵥ p.1 -
          p.2) := rfl
  have h_pair : star (Pi.single (inl a) (1 : A)) ⬝ᵥ T.splitGram *ᵥ w = w (eStar a) := by simp
  rw [h_coe, eichlerMap_mulVec, h_pair]
  simp only [star_neg, neg_dotProduct]
  module

/-- Let `A` have a trace-one element τ (τ + τ̄ = 1) and let `T.splitGram` be hermitian and
invertible. For a < ϱ, a vector v on the basis indices of floor at least a + 1 and a skew-adjoint β,
the Heisenberg element ν(v, β) of floor a lies in N_a = G_a ∩ N_(<a+1). Here ν(v, β) is the Eichler
transformation e*_a ↦ e*_a + v + (β − τh(v,v))e_a, and G_a is the group of isometries fixing every
basis vector of floor below a. -/
lemma heisenbergElem_mem_floorUnipotent : heisenbergElem (T := T) a p ∈ floorUnipotent a := by
  -- The matrix differs from `1` only in row `e_a` and in column `e*_a`, and the entries of `v`
  -- vanish on the floors at most `a`: compare the entries with those of `1`.
  set v : 𝔰.BesselIndex → A := inclMatrix A (↑) *ᵥ p.1
  set c : A := p.2 - element * star v ⬝ᵥ T.splitGram *ᵥ v
  have h_entry (i j : 𝔰.BesselIndex) :
      (heisenbergElem (T := T) a p).val.val i j =
        (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) i j +
          (Pi.single j (1 : A) : 𝔰.BesselIndex → A) (eStar a) * v i +
          (c * (Pi.single j (1 : A) : 𝔰.BesselIndex → A) (eStar a) -
            star v ⬝ᵥ T.splitGram *ᵥ Pi.single j 1) *
            (Pi.single (inl a) (1 : A) : 𝔰.BesselIndex → A) i := by
    have h_col : (heisenbergElem (T := T) a p).val.val i j =
        ((heisenbergElem (T := T) a p).val.val *ᵥ Pi.single j 1) i := by
      rw [mulVec_single_one, col_apply]
    rw [h_col, heisenbergElem_mulVec]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Matrix.one_apply, v, c]
  have hfe : floorOf (eStar a : 𝔰.BesselIndex) = a := rfl
  have hfa : floorOf (inl a : 𝔰.BesselIndex) = a := rfl
  have hle : BesselIndex.level (eStar a : 𝔰.BesselIndex) = 2 * 𝔰.ϱ - a := rfl
  have hla : BesselIndex.level (inl a : 𝔰.BesselIndex) = a := rfl
  refine Subgroup.mem_inf.2 ⟨mem_floorGroup.2 fun i j hj ↦ ?_, mem_unipotentBelow.2 fun i j h ↦ ?_⟩
  · have hj' : floorOf j ≤ a := hj.le
    have hne : (eStar a : 𝔰.BesselIndex) ≠ j := fun h_eq ↦ by
      rw [← h_eq] at hj; exact lt_irrefl _ hj
    rw [h_entry, Pi.single_eq_of_ne hne, zero_mul, mul_zero,
      inclMatrix_floor_pair_single_eq_zero a p.1 hj', sub_zero, zero_mul, add_zero, add_zero]
  · rw [h_entry]
    have h_v : (Pi.single j (1 : A) : 𝔰.BesselIndex → A) (eStar a) * v i = 0 := by
      by_cases hje : (eStar a : 𝔰.BesselIndex) = j
      · subst hje
        have hfi : floorOf i ≤ a := by
          have := floorOf_level_cases i
          rw [hfe, hle, ite_eq_left (Nat.lt_succ_self _)] at h
          split_ifs at h <;> lia
        rw [show v i = 0 from inclMatrix_floor_apply_eq_zero a p.1 hfi, mul_zero]
      · rw [Pi.single_eq_of_ne hje, zero_mul]
    have h_e : (c * (Pi.single j (1 : A) : 𝔰.BesselIndex → A) (eStar a) -
        star v ⬝ᵥ T.splitGram *ᵥ Pi.single j 1) *
        (Pi.single (inl a) (1 : A) : 𝔰.BesselIndex → A) i = 0 := by
      by_cases hie : i = inl a
      · subst hie
        rw [hfa, hla, ite_eq_left (Nat.lt_succ_self _)] at h
        have hfj : floorOf j ≤ a := by
          have := floorOf_level_cases j
          split_ifs at h <;> lia
        have hne : (eStar a : 𝔰.BesselIndex) ≠ j := by
          rintro rfl
          rw [hfe, hle, ite_eq_left (Nat.lt_succ_self _)] at h
          lia
        rw [Pi.single_eq_of_ne hne, mul_zero,
          inclMatrix_floor_pair_single_eq_zero a p.1 hfj, sub_zero, zero_mul]
      · rw [Pi.single_eq_of_ne hie, mul_zero]
    rw [h_v, h_e, add_zero, add_zero]

variable {a p q}

/-- Let `s` lie in `G_{a+1}` (`floorGroup (a + 1)`), the group fixing the basis vectors of floor at
most a. Let ν(v, β) = `heisenbergElem a (v, β)` be the Heisenberg isometry of floor a, where v is a
vector on the floors at least a + 1 and β is skew-adjoint. Then s ν(v, β) = ν(sv, β) s, where sv is
the block of s on the floors at least a + 1 applied to v. -/
lemma mul_heisenbergElem (h : s ∈ floorGroup (a + 1)) :
    s * heisenbergElem a p =
      heisenbergElem a (s.val.val.toSquareBlockProp (a + 1 ≤ floorOf ·) *ᵥ p.1, p.2) * s := by
  -- `s` fixes `e_a`, keeps the form and acts on `V_(a+1)` by its block
  set v : 𝔰.BesselIndex → A := inclMatrix A (↑) *ᵥ p.1 with hv
  have h_block :
      inclMatrix A (↑) *ᵥ s.val.val.toSquareBlockProp (a + 1 ≤ floorOf ·) *ᵥ p.1 = s.val.val *ᵥ v :=
    inclMatrix_mulVec_floor_block a.isLt h p.1
  have h_fix : s.val.val *ᵥ Pi.single (inl a) (1 : A) = Pi.single (inl a) 1 := by
    have h_point : orbitPoint a.castSucc s = Pi.single (𝔰.besselFrame a.castSucc) 1 :=
      (mem_partialUnitriangularGroup_succ_iff (by grind)).1
        (mem_partialUnitriangularGroup_of_mem_floorGroup h)
    simpa using orbitPoint_eq_iff.1 h_point
  have h_coord (w : 𝔰.BesselIndex → A) : (s.val.val *ᵥ w) (eStar a) = w (eStar a) := by
    simpa [h_fix, -mulVec_mulVec] using form_mulVec_mulVec s (Pi.single (inl a) 1) w
  refine Subtype.ext (Units.ext ?_)
  refine ext_iff_mulVec.2 fun w ↦ ?_
  simp [h_block, ← hv, ← mulVec_mulVec, mulVec_add, mulVec_smul, h_fix, h_coord, form_mulVec_mulVec]

/-- The Heisenberg group law: ν(v, β)ν(v', β') = ν(v + v', β + β' + (x − x̄)), where x = τh(v', v).
Here v and v' are vectors of the floors at least a + 1, extended by zero, β and β' are skew, h is
the form of the Gram matrix, and τ is the given element with τ + τ̄ = 1.

A special case of the composition law of Eichler–Siegel transformations on the unipotent radical of
an isotropic line's stabiliser, in matrix coordinates for one floor. -/
lemma heisenbergElem_mul :
    (heisenbergElem a p * heisenbergElem a q : T.G) =
      heisenbergElem a
        (p.1 + q.1,
          p.2 + q.2 +
            skewPart
              (element * star (inclMatrix A (↑) *ᵥ q.1) ⬝ᵥ T.splitGram *ᵥ inclMatrix A (↑) *ᵥ
                p.1)) := by
  set v : 𝔰.BesselIndex → A := inclMatrix A (↑) *ᵥ p.1 with hv
  set v' : 𝔰.BesselIndex → A := inclMatrix A (↑) *ᵥ q.1 with hv'
  -- apply both sides to a vector; the vectors `v`, `v'` and `e_a` have coordinate `0` at `e*_a`
  have hv_coord : v (eStar a) = 0 := by simp [v, inclMatrix_val_mulVec]
  have hv'_coord : v' (eStar a) = 0 := by simp [v', inclMatrix_val_mulVec]
  have h_star : star (star v' ⬝ᵥ T.splitGram *ᵥ v) = star v ⬝ᵥ T.splitGram *ᵥ v' :=
    star_dotProduct_mulVec_comm IsHermitianUnit.conjTranspose_eq v' v
  refine Subtype.ext (Units.ext ?_)
  refine ext_iff_mulVec.2 fun w ↦ ?_
  simp [← hv, ← hv', ← mulVec_mulVec, mulVec_add, mulVec_smul, hv_coord, hv'_coord, h_star,
    eq_sub_of_add_eq' (element_add_star (A := A))]
  module

/-- An isotropic vector w that vanishes on the floors below a and has coordinate 1 at e*_a is
ν(v, β)e*_a for some Heisenberg element ν(v, β) of floor a. -/
lemma exists_heisenbergElem_mulVec_eq {w : 𝔰.BesselIndex → A}
    (h_lower : ∀ j : 𝔰.BesselIndex, floorOf j < a → w j = 0) (h_top : w (eStar a) = 1)
    (h_isotropic : star w ⬝ᵥ T.splitGram *ᵥ w = 0) :
    ∃ p : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) × skewAdjoint A,
      w = (heisenbergElem (T := T) a p).val.val *ᵥ Pi.single (eStar a) 1 := by
  obtain ⟨v, d, rfl⟩ : ∃ (v : {j // a + 1 ≤ floorOf j} → A) (d : A), w = Pi.single (eStar a) 1 +
      inclMatrix A (fun j : {j // a + 1 ≤ floorOf j} ↦ j.val) *ᵥ v + d • Pi.single (inl a) 1 := by
    refine ⟨fun j ↦ w j, w (inl a), ?_⟩
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, inclMatrix_val_mulVec]
    rcases j with b | m | b
    · by_cases hba : b = a
      · subst hba; simp
      · by_cases hlt : (b : ℕ) < a
        · simp [hba, not_le.2 (Nat.lt_succ_of_lt hlt), h_lower (inl b) hlt]
        · have hge : a + 1 ≤ (b : ℕ) := by have : b.val ≠ a.val := Fin.val_ne_of_ne hba; lia
          simp [hba, hge]
    · have hge : a + 1 ≤ floorOf (inr (inl m) : 𝔰.BesselIndex) := by
        have := floorOf_level_cases (inr (inl m) : 𝔰.BesselIndex)
        have : BesselIndex.level (inr (inl m) : 𝔰.BesselIndex) = 𝔰.ϱ := rfl
        lia
      simp [hge]
    · by_cases hba : b = a
      · subst hba; simp [h_top]
      · by_cases hlt : (b : ℕ) < a
        · simp [hba, not_le.2 (Nat.lt_succ_of_lt hlt), h_lower (eStar b) hlt]
        · have hge : a + 1 ≤ (b : ℕ) := by have : b.val ≠ a.val := Fin.val_ne_of_ne hba; lia
          simp [hba, hge]
  -- isotropy determines `d + star d`, and the skew parameter supplies the rest of `d`
  set v' : 𝔰.BesselIndex → A := inclMatrix A (↑) *ᵥ v
  have hv'_eStar : star v' ⬝ᵥ T.splitGram *ᵥ Pi.single (eStar a) 1 = 0 :=
    inclMatrix_floor_pair_single_eq_zero a v le_rfl
  have hv'_inl : star v' ⬝ᵥ T.splitGram *ᵥ Pi.single (inl a) 1 = 0 :=
    inclMatrix_floor_pair_single_eq_zero a v le_rfl
  have heStar_v' : star (Pi.single (eStar a) (1 : A)) ⬝ᵥ T.splitGram *ᵥ v' = 0 := by
    rw [Pi.star_single, star_one, single_dotProduct, one_mul,
      splitGram_mulVec_apply (eStar a) a.is_lt]
    exact inclMatrix_floor_apply_eq_zero a v le_rfl
  have hinl_v' : star (Pi.single (inl a) (1 : A)) ⬝ᵥ T.splitGram *ᵥ v' = 0 := by
    rw [Pi.star_single, star_one, single_dotProduct, one_mul,
      splitGram_mulVec_apply (inl a) a.is_lt]
    exact inclMatrix_floor_apply_eq_zero a v le_rfl
  have heStar_eStar : star (Pi.single (eStar a) (1 : A)) ⬝ᵥ T.splitGram *ᵥ Pi.single (eStar a) 1 = 0 := by
    rw [Pi.star_single, star_one, single_dotProduct, one_mul,
      splitGram_mulVec_apply (eStar a) a.is_lt]
    exact Pi.single_eq_of_ne (by simp) _
  have hinl_inl : star (Pi.single (inl a) (1 : A)) ⬝ᵥ T.splitGram *ᵥ Pi.single (inl a) 1 = 0 := by
    rw [Pi.star_single, star_one, single_dotProduct, one_mul,
      splitGram_mulVec_apply (inl a) a.is_lt]
    exact Pi.single_eq_of_ne (by simp) _
  have heStar_inl : star (Pi.single (eStar a) (1 : A)) ⬝ᵥ T.splitGram *ᵥ Pi.single (inl a) 1 = 1 := by
    rw [Pi.star_single, star_one, single_dotProduct, one_mul,
      splitGram_mulVec_apply (eStar a) a.is_lt]
    exact Pi.single_eq_same _ _
  have hinl_eStar : star (Pi.single (inl a) (1 : A)) ⬝ᵥ T.splitGram *ᵥ Pi.single (eStar a) 1 = 1 := by
    rw [Pi.star_single, star_one, single_dotProduct, one_mul,
      splitGram_mulVec_apply (inl a) a.is_lt]
    exact Pi.single_eq_same _ _
  have h_trace : d + star d = -(star v' ⬝ᵥ T.splitGram *ᵥ v') := by
    rw [star_add, star_add, star_smul, mulVec_add, mulVec_add, mulVec_smul] at h_isotropic
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      heStar_eStar, heStar_v', heStar_inl, hv'_eStar, hv'_inl, hinl_eStar, hinl_v', hinl_inl,
      mul_zero, mul_one, zero_add, add_zero] at h_isotropic
    exact eq_neg_of_add_eq_zero_left (by linear_combination h_isotropic)
  use ⟨v, skewPart (star element * d)⟩
  have h_coef : star element * d - star (star element * d) -
      element * (star v' ⬝ᵥ T.splitGram *ᵥ v') = d := by
    have h_elem : star (element : A) = 1 - element := eq_sub_of_add_eq' (element_add_star (A := A))
    rw [star_mul, star_star, show star v' ⬝ᵥ T.splitGram *ᵥ v' = -(d + star d) by rw [h_trace, neg_neg],
      h_elem]
    ring
  rw [heisenbergElem_mulVec]
  rw [Pi.single_eq_same, one_smul, mul_one, hv'_eStar, sub_zero]
  change Pi.single (eStar a) 1 + v' + d • Pi.single (inl a) 1 =
    Pi.single (eStar a) 1 + v' +
      (star element * d - star (star element * d) - element * star v' ⬝ᵥ T.splitGram *ᵥ v') •
        Pi.single (inl a) 1
  rw [h_coef]

/-- Let g lie in G_a and let i be the index of e_a or e*_a. If c times column i of g has coordinate
1 at e*_a, then it equals ν(v, β)e*_a for some Heisenberg element ν(v, β) of floor a. -/
lemma exists_col_eq_heisenbergElem (i : 𝔰.BesselIndex) (c : A) (h : g ∈ floorGroup a)
    (h_floor : floorOf i = a) (h_entry : g.val (eStar a) i * c = 1) :
    ∃ p : ({ i // a + 1 ≤ floorOf i } → A) × skewAdjoint A,
      g *ᵥ Pi.single i c = (heisenbergElem (T := T) a p).val.val *ᵥ Pi.single (eStar a) 1 := by
  set w : 𝔰.BesselIndex → A := g.val.val *ᵥ Pi.single i c
  -- `w` vanishes on the floors below `a`, has the entry `1` at `e*_a`, and is isotropic
  have lower (j : 𝔰.BesselIndex) (hj : floorOf j < a) : w j = 0 := by
    have hne : j ≠ i := fun h_eq ↦ by rw [h_eq, h_floor] at hj; exact lt_irrefl _ hj
    rw [show w j = g.val.val j i * c by simp [w, mulVec_single, mul_comm],
      apply_eq_one_apply_of_mem_floorGroup h j i (.inl ⟨hj, hj.trans a.is_lt⟩),
      one_apply_ne hne, zero_mul]
  have top : w (eStar a) = 1 := by simpa [w, mul_comm] using h_entry
  have isotropic : star w ⬝ᵥ T.splitGram *ᵥ w = 0 := by
    have h_zero : star (Pi.single i c) ⬝ᵥ T.splitGram *ᵥ Pi.single i c = 0 := by
      have hi_lt : floorOf i < 𝔰.ϱ := by rw [h_floor]; exact a.is_lt
      have hne : oppositeIndex i ≠ i := by
        intro h_eq
        have hlev := level_oppositeIndex_add_level i
        rw [h_eq] at hlev
        have := floorOf_level_cases i
        lia
      rw [Pi.star_single, single_dotProduct, splitGram_mulVec_apply i hi_lt,
        Pi.single_eq_of_ne hne, mul_zero]
    exact (form_mulVec_mulVec g _ _).trans h_zero
  exact exists_heisenbergElem_mulVec_eq lower top isotropic

omit [TraceOne A] [IsHermitianUnit T.splitGram] in
/-- If g⁻¹s lies in Q_{a+1} ∩ G_a and ge*_a = se*_a, then g⁻¹s lies in G_{a+1}. -/
lemma inv_mul_mem_floorGroup_succ (h : g⁻¹ * s ∈ partialUnitriangularGroup (a + 1) ⊓ floorGroup a)
    (h_eq : g.val.val *ᵥ Pi.single (eStar a) 1 = s.val.val *ᵥ Pi.single (eStar a) 1) :
    g⁻¹ * s ∈ floorGroup (a + 1) := by
  have h_fix : (g⁻¹ * s).val.val *ᵥ Pi.single (eStar a) 1 = Pi.single (eStar a) 1 := by
    rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, ← h_eq]
    simp [mulVec_mulVec, -mulVec_single]
  refine mem_floorGroup.2 fun i j hj ↦ ?_
  by_cases h_star : j = eStar a
  · rw [h_star]
    simpa [Pi.single_apply, Matrix.one_apply] using congrFun h_fix i
  · -- the other columns of floor at most `a` are those of the identity matrix by `h`
    obtain ⟨h_unitri, h_floor⟩ := mem_inf.1 h
    by_cases hfj : floorOf j < a
    · exact h_floor i j hfj
    · have hj_eq : j = inl a := by
        rcases j with b | m | b
        · exact congrArg inl (Fin.ext (by change (b : ℕ) < _ at hj; change ¬(b : ℕ) < _ at hfj; lia))
        · exfalso
          have := floorOf_level_cases (inr (inl m) : 𝔰.BesselIndex)
          have : BesselIndex.level (inr (inl m) : 𝔰.BesselIndex) = 𝔰.ϱ := rfl
          lia
        · exfalso
          exact h_star (congrArg eStar (Fin.ext (by
            change (b : ℕ) < _ at hj; change ¬(b : ℕ) < _ at hfj; lia)))
      subst hj_eq
      by_cases hle : BesselIndex.level (inl a : 𝔰.BesselIndex) ≤ BesselIndex.level i
      · exact mem_partialUnitriangularGroup.1 h_unitri i (inl a) hle
          (.inl ⟨hj, a.val.lt_succ_self⟩)
      · have hfi : floorOf i < a := by
          have := floorOf_level_cases i
          have : BesselIndex.level (inl a : 𝔰.BesselIndex) = a := rfl
          lia
        exact apply_eq_one_apply_of_mem_floorGroup h_floor i (inl a) (.inl ⟨hfi, hfi.trans a.is_lt⟩)

/-- For a < ϱ and g in Q_{a+1} ∩ G_a, there is a Heisenberg element ν(v, β) of floor a such that
g⁻¹ν(v, β) lies in G_{a+1}. -/
lemma exists_heisenbergElem_mem_floorGroup
    (h : g ∈ partialUnitriangularGroup (a + 1) ⊓ floorGroup a) :
    ∃ p : ({ i // a + 1 ≤ floorOf i } → A) × skewAdjoint A,
      g⁻¹ * heisenbergElem a p ∈ floorGroup (a + 1) := by
  -- `g e*_a` has the entry `1` at `e*_a`, so it is the image of `e*_a` under some
  -- `heisenbergElem a p`
  have entry : g.val (eStar a) (eStar a) * 1 = 1 := by
    rw [mul_one, partialUnitriangularGroup_apply_eStar h.1 a.val.lt_succ_self (eStar a)
      (fun b hb h_eq ↦ hb.ne' (by simpa using h_eq)), one_apply_eq]
  obtain ⟨p, hp⟩ : ∃ p : ({ i // a + 1 ≤ floorOf i } → A) × skewAdjoint A,
      g.val.val *ᵥ Pi.single (eStar a) 1 =
        (heisenbergElem (T := T) a p).val.val *ᵥ Pi.single (eStar a) 1 :=
    exists_col_eq_heisenbergElem (eStar a) 1 h.2 rfl entry
  obtain ⟨h_floor, h_unip⟩ := heisenbergElem_mem_floorUnipotent (T := T) a p
  have h_mem : g⁻¹ * heisenbergElem a p ∈ partialUnitriangularGroup (a + 1) ⊓ floorGroup a :=
    mul_mem (inv_mem h) ⟨unipotentBelow_le_partialUnitriangularGroup h_unip, h_floor⟩
  exact ⟨p, inv_mul_mem_floorGroup_succ h_mem hp⟩

/-- An element of `Q_(l+1) ∩ G_l` is a product of an element of `G_(l+1)` and one of `N_l`. -/
lemma exists_floorGroup_mul_floorUnipotent
    (h : s ∈ partialUnitriangularGroup (l + 1) ⊓ floorGroup l) :
    ∃ g ∈ floorGroup (l + 1), ∃ ν ∈ floorUnipotent l, s = g * ν := by
  by_cases hl : l < 𝔰.ϱ
  · obtain ⟨p, hp⟩ := exists_heisenbergElem_mem_floorGroup (a := ⟨l, hl⟩) (inv_mem h)
    refine ⟨s⁻¹⁻¹ * heisenbergElem ⟨l, hl⟩ p, hp, (heisenbergElem ⟨l, hl⟩ p)⁻¹, ?_, by simp⟩
    exact inv_mem (heisenbergElem_mem_floorUnipotent ⟨l, hl⟩ p)
  · -- floor `l` has no hyperbolic pair, and `s` itself lies in `floorGroup (l + 1)`
    refine ⟨s, mem_floorGroup.2 fun i j hj ↦ ?_, 1, one_mem _, by simp⟩
    by_cases hfj : floorOf j < l
    · exact h.2 i j hfj
    · have h_eq_l : floorOf j = l := by lia
      by_cases hle : BesselIndex.level j ≤ BesselIndex.level i
      · have hj_lev : BesselIndex.level j < l + 1 := by
          have := floorOf_level_cases j; lia
        exact mem_partialUnitriangularGroup.1 h.1 i j hle (.inl ⟨hj, hj_lev⟩)
      · have h_lj : BesselIndex.level j = 𝔰.ϱ := by have := floorOf_level_cases j; lia
        have hfi : floorOf i < 𝔰.ϱ := by have := floorOf_level_cases i; lia
        exact apply_eq_one_apply_of_mem_floorGroup h.2 i j (.inl ⟨by lia, hfi⟩)

/-- Every element s of Q_j (unitriangular on the first j frame vectors) is a product s = γν with γ
in G_j (fixing the basis vectors of floor below j) and ν in N_(<j) (`unipotentBelow j`). -/
lemma exists_floorGroup_mul_unipotentBelow {j : ℕ} (hs : s ∈ partialUnitriangularGroup j) :
    ∃ γ ∈ floorGroup j, ∃ ν ∈ unipotentBelow j, s = γ * ν := by
  induction j with
  | zero => exact ⟨s, by simp, 1, one_mem _, (mul_one s).symm⟩
  | succ j ih =>
    obtain ⟨γ, hγ, ν, hν, rfl⟩ := ih (by grind)
    have hν_succ : ν ∈ unipotentBelow (j + 1) := unipotentBelow_le_succ hν
    have hγ_unitri : γ ∈ partialUnitriangularGroup (j + 1) :=
      (mul_mem_cancel_right (unipotentBelow_le_partialUnitriangularGroup hν)).1 hs
    obtain ⟨g, hg, n, hn, rfl⟩ := exists_floorGroup_mul_floorUnipotent ⟨hγ_unitri, hγ⟩
    exact ⟨g, hg, n * ν, mul_mem hn.2 hν_succ, mul_assoc g n ν⟩

/-- Let `A` have a trace-one element and let the Gram matrix `T.splitGram` of the whole space be
hermitian and invertible. Then an isometry s lies in the Bessel subgroup `besselS`, the subgroup
generated by `besselU` and `besselH`, if and only if s = uh. Here u lies in `besselU`, the
isometries that are block upper unitriangular for the levels with identity middle block, and h lies
in `besselH`, the isometries fixing every basis vector of floor at most ϱ (the `e_a`, the `e*_a` and
`z`). -/
lemma _root_.New.mem_besselS : s ∈ besselS ↔ ∃ u ∈ besselU, ∃ h ∈ besselH, s = u * h := by
  constructor
  · -- `s = h * ν = (h * ν * h⁻¹) * h`, and `h` normalises `unipotentBelow`
    intro hs
    obtain ⟨h, hh, ν, hν, rfl⟩ := exists_floorGroup_mul_unipotentBelow hs
    exact ⟨h * ν * h⁻¹, unipotentBelow_le_besselU (conj_mem_unipotentBelow hh hν), h, hh, by simp⟩
  · rintro ⟨u, hu, h, hh, rfl⟩
    exact mul_mem (mem_partialUnitriangularGroup_of_mem_besselU hu)
      (mem_partialUnitriangularGroup_of_mem_floorGroup hh)

/-- If the Gram matrix of the whole space is hermitian and invertible, then the Bessel subgroup
`besselS` normalises `besselU0`, the group of the elements of `besselU` that fix the frame. -/
lemma besselS_le_normalizer_besselU0 : T.besselS ≤ Subgroup.normalizer T.besselU0 := by
  refine le_normalizer_iff.2 fun s hs u hu ↦ ?_
  obtain ⟨hu, h_frame⟩ := mem_besselU0_iff.1 hu
  refine mem_besselU0_iff.2 ⟨(besselS_le_normalizer_besselU hs u).1 hu, ?_⟩
  -- with `s⁻¹ = v * h`, the frame block ignores `h` and is multiplicative in `u` and `v`
  obtain ⟨v, hv, h, hh, hs_inv⟩ := mem_besselS.1 (inv_mem hs)
  calc
    frameMatrix (s * u * s⁻¹) = frameMatrix s * frameMatrix u * frameMatrix v := by
      rw [hs_inv, ← mul_assoc, frameMatrix_mul_besselH _ hh, frameMatrix_mul hv, frameMatrix_mul hu]
    _ = frameMatrix (s * s⁻¹) := by
      rw [h_frame, mul_one, hs_inv, ← mul_assoc, frameMatrix_mul_besselH _ hh, frameMatrix_mul hv]
    _ = 1 := by simpa using (mem_besselU0_iff.1 (one_mem T.besselU0)).2

/-- Induction along the groups N_(<j), for a hermitian invertible Gram matrix. Suppose C 0 1 holds,
and C j ν implies C (j+1) (γν) for all γ in N_j. Then C j s holds for every s in N_(<j). -/
lemma unipotentBelow_induction {C : ℕ → T.G → Prop} (h_one : C 0 1)
    (h_step : ∀ j : ℕ, ∀ γ ∈ floorUnipotent j, ∀ ν : T.G, C j ν → C (j + 1) (γ * ν)) (j : ℕ) :
    ∀ s ∈ unipotentBelow j, C j s := by
  induction j with
  | zero =>
    intro s hs
    have h_eq : s = 1 :=
      eq_one_of_mem_floorGroup_inf ⟨floorGroup_zero.ge (mem_top s), hs⟩ (Or.inl le_rfl)
    rwa [h_eq]
  | succ j ih =>
    intro s hs
    -- write `s = γ * ν` with `γ ∈ floorGroup j` and `ν ∈ unipotentBelow j`; then `γ = s * ν⁻¹` lies
    -- in `unipotentBelow (j + 1)`
    obtain ⟨γ, hγ, ν, hν, rfl⟩ :=
      exists_floorGroup_mul_unipotentBelow (j := j) (unipotentBelow_le_partialUnitriangularGroup hs)
    have γ_mem : γ ∈ unipotentBelow (j + 1) :=
      (mul_mem_cancel_right (unipotentBelow_le_succ hν)).1 hs
    exact h_step j γ ⟨hγ, γ_mem⟩ ν (ih ν hν)

/-- Let `A` have a trace-one element τ and let `T.splitGram` be hermitian and invertible. For a < ϱ,
every g in N_a = G_a ∩ N_(<a+1) equals a Heisenberg element ν(v, β) of floor a, for some vector v on
the indices of floor at least a + 1 and some skew-adjoint β. Here ν(v, β) is the Eichler
transformation e*_a ↦ e*_a + v + (β − τh(v,v))e_a.

A weaker form of the standard parametrization of the unipotent radical of an isotropic line's
stabiliser by Eichler–Siegel transformations. It gives existence only, for one floor, without
uniqueness of parameters. -/
lemma exists_eq_heisenbergElem_of_mem (h : g ∈ floorUnipotent a) :
    ∃ p : ({ i // a + 1 ≤ floorOf i } → A) × skewAdjoint A, g = heisenbergElem a p := by
  obtain ⟨p, hp⟩ : ∃ p : ({ i // a + 1 ≤ floorOf i } → A) × skewAdjoint A,
      g⁻¹ * heisenbergElem a p ∈ floorGroup (a + 1) :=
    exists_heisenbergElem_mem_floorGroup ⟨unipotentBelow_le_partialUnitriangularGroup h.2, h.1⟩
  -- `g⁻¹ * heisenbergElem a p` lies in both `floorGroup (a + 1)` and `unipotentBelow (a + 1)`, so
  -- it is `1`
  have h_nilp : g⁻¹ * heisenbergElem a p ∈ unipotentBelow (a + 1) :=
    (mul_mem (inv_mem h) (heisenbergElem_mem_floorUnipotent a p)).2
  exact ⟨p, inv_mul_eq_one.1 (eq_one_of_mem_floorGroup_inf ⟨hp, h_nilp⟩ (by simp))⟩

/-- Let `A` have a trace-one element τ (τ + τ̄ = 1) and let `T.splitGram` be hermitian and
invertible, with h(v, w) = v* · `T.splitGram` · w. For a < ϱ, a vector v on the indices of floor at
least a + 1 (extended by zero) and a skew-adjoint β, the inverse of the Heisenberg element ν(v, β)
of floor a is ν(−v, x − x̄ − β), where x = τh(v, v). -/
lemma heisenbergElem_inv :
    (heisenbergElem (T := T) a p)⁻¹ =
      heisenbergElem a
        (-p.1,
          skewPart
            (element *
              star (inclMatrix A (↑) *ᵥ p.1) ⬝ᵥ T.splitGram *ᵥ inclMatrix A (↑) *ᵥ p.1) - p.2) := by
  refine inv_eq_of_mul_eq_one_right (heisenbergElem_mul.trans ?_)
  ext : 2
  -- the vectors cancel and so do the two corrections `x − x̄`
  simp [heisenbergElem, eichlerMap, mulVec_neg]

/-- The Heisenberg element ν(v, β) of floor a acts on the frame by a matrix that differs from `1`
only in row a, by the products −h(v, f_c) with the frame vectors. -/
lemma frameMatrix_heisenbergElem :
    frameMatrix (heisenbergElem (T := T) a p) =
      1 - vecMulVec (Pi.single a.castSucc 1) fun c : Fin (𝔰.ϱ + 1) ↦
        star (inclMatrix A (↑) *ᵥ p.1) ⬝ᵥ T.splitGram *ᵥ Pi.single (𝔰.besselFrame c) 1 := by
  refine Matrix.ext fun b c ↦ ?_
  have h_dual : (Pi.single (𝔰.besselFrame c) 1 : 𝔰.BesselIndex → A) (eStar a) = 0 := by
    cases c using Fin.lastCases <;> simp
  have h_col : frameMatrix (heisenbergElem (T := T) a p) b c =
      ((heisenbergElem (T := T) a p).val.val *ᵥ Pi.single (𝔰.besselFrame c) 1)
        (𝔰.besselFrame b) := by
    simp [frameMatrix, -heisenbergElem_mulVec]
  rw [h_col, heisenbergElem_mulVec, h_dual, ← besselFrame_castSucc]
  simp [vecMulVec_apply, Pi.single_apply, Matrix.one_apply, besselFrame_injective.eq_iff,
    sub_eq_add_neg, -besselFrame_castSucc]

/-- Let s be in G_{a+1}, so that s fixes the basis vectors of floor below a + 1. Let v be a vector
of the floors at least a + 1, extended by zero, let β be skew, and let ν(v,
β) = `heisenbergElem a (v, β)` be the Eichler transformation e*_a ↦ e*_a + v + (β − τh(v,v))e_a.
Then the sum of the entries just above the diagonal of the block of sν(v, β)s⁻¹ on the frame (f_0,
…, f_ϱ) = (e_0, …, e_(ϱ-1), z) equals −h(v, s⁻¹f_{a+1}), where s⁻¹f_{a+1} is
`orbitPoint a.succ s`. -/
lemma simpleRootSum_conj_heisenbergElem (hs : s ∈ floorGroup (a + 1)) :
    simpleRootSum (s * heisenbergElem a p * s⁻¹) =
      -(star (inclMatrix A (↑) *ᵥ p.1) ⬝ᵥ T.splitGram *ᵥ orbitPoint a.succ s) := by
  -- conjugation by `s` applies `s` to the vector of the Heisenberg element
  rw [mul_heisenbergElem hs, mul_inv_cancel_right, ← form_mulVec_mulVec s,
    ← inclMatrix_mulVec_floor_block a.isLt hs, orbitPoint_eq_iff.1 rfl]
  -- the entries at the simple roots are read off the matrix on the frame
  change ∑ b : Fin 𝔰.ϱ, frameMatrix (heisenbergElem (T := T) a _) b.castSucc b.succ = _
  simp [frameMatrix_heisenbergElem, vecMulVec_apply, Pi.single_apply, (Fin.castSucc_lt_succ ..).ne]

end FloorGroups

variable [TopologicalSpace A] [MeasureSpace A] [P : Place A]
  (ι : Type) [Fintype ι] [DecidableEq ι] (T : 𝔰.Form A) (m : ℕ)
  {n k Z : Type} [Fintype n] [Fintype k] [DecidableEq k]

/-! ### The Haar measure of `V_l` -/

/-- Haar measure of `V_l`, as a measure on all vectors: the image of the volume on the coordinates
of floor at least `l` under extension by zero. -/
abbrev FloorGroups.floorVolume (l : ℕ) : Measure (𝔰.BesselIndex → A) :=
  Measure.map (fun v ↦ inclMatrix A (Subtype.val : {i // l ≤ floorOf i} → 𝔰.BesselIndex) *ᵥ v)
    volume

/-! ### Hyperbolic bases, Weyl elements and changes of coordinates -/

/-- A basis of the middle space `V_ϱ`, which has Gram matrix `T` and rank `𝔰.k + 1`: a first
hyperbolic pair, `m` more pairs and an orthonormal part indexed by `ι`. So there are
`card ι + 2 * m + 2` basis vectors, and the field `card_eq` equates the two counts. As the modulus
of `det T` is 1, the change of coordinates preserves volume
(`New.Floors.HyperbolicBasis.measurePreserving_mulVec`). -/
structure HyperbolicBasis where
  /-- The matrix whose columns are the basis vectors. -/
  basisMatrix : Matrix 𝔰.MiddleIndex (Fin 2 ⊕ SplitIndex m ι) A
  /-- The Gram matrix of the basis for `T`: m + 1 hyperbolic planes and an orthonormal part. -/
  gram_eq : basisMatrixᴴ * T * basisMatrix = planeSumGram (hyperbolicGram (Fin m) 1)
  /-- The number of basis vectors is the rank of V_ϱ. -/
  card_eq : 𝔰.k + 1 = card ι + 2 * m + 2
  /-- The modulus of the determinant of `T` is 1. -/
  modulus_det : P.modulus T.det = 1

variable {ι T m} (F : HyperbolicBasis ι T m) (b : Fin 𝔰.n) [MeasurableSpace Z] {ζ : Measure Z}

/-- The image of the measure md(c)^{d_l} dc on A under c ↦ w_l(c)⁻¹, where w_l(c) is the Weyl
element of floor l and d_l = `𝔰.k` + 1 + 2(ϱ − (l + 1)), the subtraction being truncated. -/
abbrev Place.weylLaw (l : ℕ) : Measure T.G :=
  (volume.withDensity fun c ↦ modulus c ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (l + 1)))).map fun c ↦
    (floorWeyl l c)⁻¹

/-- Reindexing the coordinates along a bijection preserves the volume. -/
lemma measurePreserving_inclMatrix (g : n ≃ k) : MeasurePreserving (inclMatrix A g *ᵥ ·) := by
  have h_eq : (inclMatrix A g *ᵥ ·) =
      (MeasurableEquiv.piCongrLeft (fun _ : n ↦ A) g.symm).symm := by
    ext v i
    simp [inclMatrix, submatrix_mulVec_equiv, MeasurableEquiv.piCongrLeft]
  rw [h_eq]
  exact (measurePreserving_piCongrLeft _ g.symm).symm

omit [TopologicalSpace A] [MeasureSpace A] [Place A] in
/-- The Gram matrix of the standard basis vectors `e_(g j)` for `J` is the submatrix of `J` on the
indices `g j`. -/
lemma gram_inclMatrix {n : Type*} (g : n → k) (J : Matrix k k A) :
    (inclMatrix A g)ᴴ * J * inclMatrix A g = J.submatrix g g := by
  simp [inclMatrix, Matrix.mul_apply, ← ext_iff, Matrix.one_apply]

/-- If `f` enumerates the basis indices of `V_l` without repetition, then extension by zero along
`f` carries the volume of `n → A` to the Haar measure of `V_l`. -/
lemma map_inclMatrix_eq_floorVolume (f : n → 𝔰.BesselIndex)
    (hf_inj : Injective f := by intro; simp)
    (hf_range : ∀ i : 𝔰.BesselIndex, i ∈ Set.range f ↔ l ≤ floorOf i := by simp) :
    volume.map (inclMatrix A f *ᵥ ·) = floorVolume l := by
  -- `f` factors through a bijection `e` onto the indices of `V_l`, which permutes the coordinates
  let e : n ≃ {i : 𝔰.BesselIndex // l ≤ floorOf i} :=
    (Equiv.ofInjective f hf_inj).trans (.subtypeEquivRight hf_range)
  have h_incl : inclMatrix A (Subtype.val : {i : 𝔰.BesselIndex // l ≤ floorOf i} → 𝔰.BesselIndex) *
      inclMatrix A e = inclMatrix A f := mul_inclMatrix ..
  rw [floorVolume, ← (measurePreserving_inclMatrix e).map_eq]
  simp (disch := fun_prop) [Measure.map_map, comp_def, h_incl]

/-- Extension by zero from the middle block carries the volume to the Haar measure of `V_ϱ`. -/
lemma map_inclMatrix_middle_eq_floorVolume :
    volume.map (inclMatrix A (inr ∘ inl : 𝔰.MiddleIndex → 𝔰.BesselIndex) *ᵥ ·) =
      floorVolume 𝔰.top :=
  map_inclMatrix_eq_floorVolume _ (inr_injective.comp inl_injective) (by simp)

/-- The indices of the hyperbolic pairs of `V_b` after the first: the `m` other pairs of `V_ϱ`, and
the pairs `e_a`, `e*_a` with `b ≤ a`. -/
abbrev FloorPairs (m : ℕ) : Type := Fin m ⊕ {i : Fin 𝔰.ϱ // b.val ≤ i}

/-- The basis of `V_b` made of the basis `F` of `V_ϱ` and the pairs `e_a`, `e*_a` with `b ≤ a`, as
the columns of a matrix. It is the block matrix of `F.basisMatrix` and the identity on these pairs,
with its rows placed among the basis indices and its columns reordered. The columns are listed in
`New.Floors.HyperbolicBasis.col_floorBasis`, and the Gram matrix is computed in
`New.Floors.HyperbolicBasis.gram_floorBasis`. -/
def HyperbolicBasis.floorBasis :
    Matrix 𝔰.BesselIndex (Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m) A :=
  let S : Type := {i : Fin 𝔰.ϱ // b.val ≤ i}
  -- the basis indices of `V_b`: the middle block, then the `e_a` and the `e*_a` with `b ≤ a`
  let incl : 𝔰.MiddleIndex ⊕ S ⊕ S → 𝔰.BesselIndex := inr ∘ inl ⊕ᵥ Sum.map (↑) (inr ∘ (↑))
  -- the new order: the first pair of `F.basisMatrix`; the first vectors of the other pairs; the
  -- orthonormal part; the second vectors of the other pairs
  let order : Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → (Fin 2 ⊕ SplitIndex m ι) ⊕ S ⊕ S :=
    inl ∘ inl ⊕ᵥ
      (Sum.map (inr ∘ inl) inl ⊕ᵥ (inl ∘ inr ∘ inr ∘ inl ⊕ᵥ Sum.map (inr ∘ inr ∘ inr) inr))
  inclMatrix A incl * F.basisMatrix.fromBlocks 0 0 (diagonal (n := S ⊕ S) 1) * inclMatrix A order

omit [StarRing A] [TopologicalSpace A] [MeasureSpace A] [Place A] in
private lemma planeSumGram_hyperbolicGram_sq {α : Type} [Fintype α] [DecidableEq α] :
    planeSumGram (hyperbolicGram α (1 : Matrix ι ι A)) *
      planeSumGram (hyperbolicGram α (1 : Matrix ι ι A)) = 1 := by
  simp only [planeSumGram, hyperbolicGram, fromBlocks_multiply, fromCols_mul_fromRows,
    fromCols_mul_fromBlocks, fromBlocks_mul_fromRows, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.mul_one, add_zero, zero_add]
  simp [← ext_iff, Matrix.one_apply]
/-- The Gram matrix of `F.floorBasis b` consists of a hyperbolic plane for the first pair, one for
each pair indexed by `FloorPairs b m`, and an orthonormal part indexed by `ι`. -/
lemma HyperbolicBasis.gram_floorBasis :
    (F.floorBasis b)ᴴ * T.splitGram * F.floorBasis b =
      planeSumGram (hyperbolicGram (FloorPairs b m) (1 : Matrix ι ι A)) := by
  -- on the basis vectors of `V_b` the form is `T` plus hyperbolic planes; `F.gram_eq` handles `T`
  let S : Type := {i : Fin 𝔰.ϱ // b.val ≤ i}
  let incl : 𝔰.MiddleIndex ⊕ S ⊕ S → 𝔰.BesselIndex := inr ∘ inl ⊕ᵥ Sum.map (↑) (inr ∘ (↑))
  have block : T.splitGram.submatrix incl incl = T.fromBlocks 0 0 (fromBlocks 0 1 1 0) := by
    ext (x | x | x) (y | y | y) <;>
      simp [incl, splitGram, Matrix.one_apply, Subtype.coe_inj]
  rw [floorBasis, gram_mul, gram_inclMatrix, gram_mul, gram_inclMatrix, block]
  simp [F.gram_eq, fromBlocks_conjTranspose, fromBlocks_multiply, ← ext_iff, Matrix.one_apply]

/-- Multiplication by `F.basisMatrix`, the matrix of the hyperbolic basis `F` of `V_ϱ`, preserves
the volume of coordinate vectors. -/
lemma HyperbolicBasis.measurePreserving_mulVec : MeasurePreserving (F.basisMatrix *ᵥ ·) := by
  -- Reindex the columns by `e` to get a square matrix `M`. Its Gram matrix has square one.
  let e : 𝔰.MiddleIndex ≃ Fin 2 ⊕ SplitIndex m ι := equivOfCardEq (by simp +arith [F.card_eq])
  let M : Matrix 𝔰.MiddleIndex 𝔰.MiddleIndex A := F.basisMatrix * inclMatrix A e
  have gram_sq : (Mᴴ * T * M) ^ 2 = 1 := by
    rw [gram_mul, sq, gram_inclMatrix, F.gram_eq, submatrix_mul_equiv _ _ _ e,
      planeSumGram_hyperbolicGram_sq, submatrix_one_equiv]
  have h_left : Mᴴ * T * M * (Mᴴ * T) * M = 1 := by rw [Matrix.mul_assoc _ _ M, ← sq, gram_sq]
  have h_unit : IsUnit M.det := isUnit_det_of_left_inverse h_left
  -- Taking determinants, `modulus M.det ^ 4 = 1`, since `modulus T.det = 1`.
  have h_md : P.modulus M.det = 1 := by
    have h_det : P.modulus ((Mᴴ * T * M) ^ 2).det = 1 := by simp [gram_sq]
    simpa [F.modulus_det, ← sq, toNNReal_eq_one_iff] using congrArg ENNReal.toNNReal h_det
  have h_vol : volume.map (M *ᵥ ·) = volume := by simp [P.map_mulVec_volume _ M h_unit, h_md]
  refine ⟨by fun_prop, ?_⟩
  simpa (disch :=
    fun_prop) [← (measurePreserving_inclMatrix e).map_eq, Measure.map_map, ↓ comp_def] using h_vol

/-- The basis `F.floorBasis b` carries the volume of its coordinates to the Haar measure of
`V_b`. -/
lemma HyperbolicBasis.map_floorBasis_volume :
    volume.map (F.floorBasis b *ᵥ ·) = FloorGroups.floorVolume b := by
  let S : Type := {i : Fin 𝔰.ϱ // b.val ≤ i}
  let incl : 𝔰.MiddleIndex ⊕ S ⊕ S → 𝔰.BesselIndex := inr ∘ inl ⊕ᵥ Sum.map (↑) (inr ∘ (↑))
  let order : Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → (Fin 2 ⊕ SplitIndex m ι) ⊕ S ⊕ S :=
    inl ∘ inl ⊕ᵥ
      (Sum.map (inr ∘ inl) inl ⊕ᵥ (inl ∘ inr ∘ inr ∘ inl ⊕ᵥ Sum.map (inr ∘ inr ∘ inr) inr))
  have h_incl_inj : Injective incl := by
    rintro (x | x | x) (y | y | y) h
    · exact congrArg inl (inl_injective (inr_injective h))
    · simp [incl] at h
    · simp [incl] at h
    · simp [incl] at h
    · exact congrArg (inr ∘ inl) (Subtype.ext (inl_injective h))
    · simp [incl] at h
    · simp [incl] at h
    · simp [incl] at h
    · exact congrArg (inr ∘ inr) (Subtype.ext (inr_injective (inr_injective h)))
  have h_incl_range (i : 𝔰.BesselIndex) : i ∈ Set.range incl ↔ b.val ≤ floorOf i := by
    rcases i with a | x | a
    · constructor
      · rintro ⟨(y | y | y), hy⟩
        · exact absurd hy (by simp [incl])
        · have hya : y.1 = a := inl_injective hy
          simpa [hya] using y.2
        · exact absurd hy (by simp [incl])
      · intro ha
        exact ⟨inr (inl ⟨a, ha⟩), rfl⟩
    · constructor
      · intro _
        have := floorOf_level_cases (inr (inl x) : 𝔰.BesselIndex)
        have : BesselIndex.level (inr (inl x) : 𝔰.BesselIndex) = 𝔰.ϱ := rfl
        have := b.is_le
        lia
      · intro _
        exact ⟨inl x, rfl⟩
    · constructor
      · rintro ⟨(y | y | y), hy⟩
        · exact absurd hy (by simp [incl])
        · exact absurd hy (by simp [incl])
        · have hya : y.1 = a := inr_injective (inr_injective hy)
          simpa [hya] using y.2
      · intro ha
        exact ⟨inr (inr ⟨a, ha⟩), rfl⟩
  have h_incl : volume.map (inclMatrix A incl *ᵥ ·) = FloorGroups.floorVolume b :=
    map_inclMatrix_eq_floorVolume incl h_incl_inj h_incl_range
  let orderEquiv : Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m ≃
      (Fin 2 ⊕ SplitIndex m ι) ⊕ S ⊕ S :=
    { toFun := order
      invFun := fun
        | inl (inl i) => inl i
        | inl (inr (inl c)) => inr (inl (inl c))
        | inl (inr (inr (inl i))) => inr (inr (inl i))
        | inl (inr (inr (inr c))) => inr (inr (inr (inl c)))
        | inr (inl a) => inr (inl (inr a))
        | inr (inr a) => inr (inr (inr (inr a)))
      left_inv := by rintro (i | (c | a) | i | c | a) <;> rfl
      right_inv := by rintro ((i | c | i | c) | a | a) <;> rfl }
  simp only [floorBasis, diagonal_one', ← mulVec_mulVec, fromBlocks_mulVec, zero_mulVec, add_zero,
    one_mulVec, zero_add]
  -- The map permutes the coordinates, splits off those of the pairs `e_a`, `e*_a` with `b ≤ a`,
  -- applies `F.basisMatrix` to the others, and includes the result as `V_b`. Each step preserves
  -- volume.
  exact (MeasurePreserving.comp ⟨by fun_prop, h_incl⟩
    (measurePreserving_sumElim.comp
      ((F.measurePreserving_mulVec.prod (.id _)).comp
        ((measurePreserving_sumPiEquivProdPi _).comp
          (measurePreserving_inclMatrix orderEquiv))))).map_eq

variable {μ ν : Measure T.G} [SFinite μ] [SFinite ν]
  (σ : ℕ → Measure T.G) [∀ l, SFinite (σ l)]
  {i j : ℕ} {s : T.G} {S : Subgroup T.G} {f : T.G → ℝ≥0∞}

/-- The measure `η_l` on the unitary group. For `l < ϱ` it is the image of the Haar measure of
`V_(l+1)` times the skew measure of the place, under the Heisenberg parametrisation
`New.Floors.TraceOne.heisenbergElem` of `N_l`. Otherwise it is the unit mass at `1`. -/
def Place.heisenbergMeasure [H : IsHermitianUnit T.splitGram] (l : ℕ) : Measure (U T.splitGram) :=
  if h : l < 𝔰.ϱ then (volume.prod P.skewMeasure).map (heisenbergElem (T := T) ⟨l, h⟩) else dirac 1

/-- The group `G_l` is a measurable set: finitely many entries are prescribed. -/
lemma measurableSet_floorGroup : MeasurableSet (T.floorGroup l : Set T.G) :=
  (isClosed_of_entries_eq_one mem_floorGroup).measurableSet

@[simp]
lemma heisenbergMeasure_eq_dirac_one [H : IsHermitianUnit T.splitGram]
    (h : 𝔰.ϱ ≤ l) : heisenbergMeasure l = dirac (1 : T.G) :=
  dite_eq_right h.not_gt

@[fun_prop]
lemma continuous_orbitPoint : Continuous (orbitPoint b : T.G → 𝔰.BesselIndex → A) := by
  fun_prop [orbitPoint]

variable [H : IsHermitianUnit T.splitGram] in
instance : SFinite (heisenbergMeasure l : Measure T.G) := by
  dsimp only [heisenbergMeasure]; split_ifs <;> infer_instance

/-- The unitary group is closed in the space of matrices, with the subspace topology. -/
lemma isClosedEmbedding_unitary_coe [H : IsHermitianUnit T.splitGram] :
    Topology.IsClosedEmbedding fun g : T.G ↦ (g : GL 𝔰.BesselIndex A).val :=
  Matrix.unitaryGroupOf.isClosedEmbedding_val H.isUnit

/-- A function with values in the unitary group is measurable if it is measurable as a function
with values in matrices. -/
lemma measurable_unitary_of_coe [H : IsHermitianUnit T.splitGram] {f : Z → T.G}
    (hf : Measurable fun z : Z ↦ (f z : GL 𝔰.BesselIndex A).val) : Measurable f :=
  isClosedEmbedding_unitary_coe.measurableEmbedding.measurable_comp_iff.1 hf

@[fun_prop]
lemma continuous_weylElem [H : IsHermitianUnit T.splitGram] :
    Continuous (weylElem 𝔰.ϱ : (ℕ → Aˣ) → T.G) := by
  refine isClosedEmbedding_unitary_coe.continuous_iff.2 (continuous_matrix fun i j ↦ ?_)
  simp only [Function.comp_apply, weylElem, weylOn, Units.isUnit, and_true, and_self,
    ↓inverse_star_unit, Pi.star_apply, isUnit_star, star_star, Ring.inverse_invertible, invOf_units,
    of_apply]
  -- each entry is constant, a parameter, or its conjugate inverse
  split_ifs <;> fun_prop

@[fun_prop]
lemma measurable_floorWeyl [H : IsHermitianUnit T.splitGram] :
    Measurable (floorWeyl l : A → T.G) := by
  classical
  have h_isUnit : MeasurableSet {c : A | IsUnit c} :=
    measurableEmbedding_units_val.measurableSet_range
  refine measurable_unitary_of_coe
    (measurable_pi_iff.2 fun i ↦ measurable_pi_iff.2 fun j ↦ ?_)
  simp only [floorWeyl, weylOn, of_apply]
  by_cases hfl : floorOf j = l
  · by_cases hlt : l < 𝔰.ϱ
    · simp only [hfl, hlt, true_and]
      by_cases hlev : BesselIndex.level j < 𝔰.ϱ
      · simp only [hlev, ↓reduceIte]
        have h_eq : (fun c : A ↦
            if i = if IsUnit c then oppositeIndex j else j then
              if IsUnit c then c else 1
            else 0) =
            fun c : A ↦ if IsUnit c then (if i = oppositeIndex j then c else 0)
              else (if i = j then 1 else 0) :=
          funext fun c ↦ by by_cases hu : IsUnit c <;> simp [hu]
        rw [h_eq]
        refine Measurable.ite h_isUnit ?_ ?_
        · by_cases hi : i = oppositeIndex j
          · simp only [hi, ↓reduceIte]; exact measurable_id
          · simp only [hi, ↓reduceIte]; exact measurable_const
        · exact measurable_const
      · simp only [hlev, ↓reduceIte]
        have h_eq : (fun c : A ↦
            if i = if IsUnit c then oppositeIndex j else j then
              if IsUnit c then Ring.inverse (star c) else 1
            else 0) =
            fun c : A ↦ if IsUnit c then (if i = oppositeIndex j then Ring.inverse (star c) else 0)
              else (if i = j then 1 else 0) :=
          funext fun c ↦ by by_cases hu : IsUnit c <;> simp [hu]
        rw [h_eq]
        refine Measurable.ite h_isUnit ?_ ?_
        · by_cases hi : i = oppositeIndex j
          · simp only [hi, ↓reduceIte]; fun_prop
          · simp only [hi, ↓reduceIte]; exact measurable_const
        · exact measurable_const
    · simp only [hfl, hlt, false_and, and_false, ↓reduceIte]; exact measurable_const
  · simp only [hfl, false_and, ↓reduceIte]; exact measurable_const

@[fun_prop]
lemma continuous_heisenbergElem [H : IsHermitianUnit T.splitGram]
    {a : Fin 𝔰.ϱ} : Continuous (heisenbergElem (T := T) a) := by
  refine isClosedEmbedding_unitary_coe.continuous_iff.2 ?_
  simp only [↓comp_def, heisenbergElem, eichlerMap, star_neg, mulVec_mulVec, Pi.star_single,
    star_one, single_vecMul, one_smul, val_of_coe]
  fun_prop

/-- An element `s` of `G_l` acts on the coordinates of floor at least `l` by a block that preserves
their volume. -/
lemma measurePreserving_floor_block_mulVec [H : IsHermitianUnit T.splitGram]
    (h : s ∈ floorGroup l) :
    MeasurePreserving fun v : { a // l ≤ floorOf a } → A ↦
      (s : GL 𝔰.BesselIndex A).val.toSquareBlockProp (l ≤ floorOf ·) *ᵥ v := by
  -- `s` is block triangular with the identity on the indices of floor below `l`, so the block has
  -- the determinant of `s`, which has norm one
  have outside : s.val.val.toSquareBlockProp (¬l ≤ floorOf ·) = 1 := by
    ext i j
    have h_entry : s.val.val i j = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) i j :=
      h i j (not_le.1 j.2)
    simpa [toSquareBlockProp_def, Matrix.one_apply, Subtype.ext_iff] using h_entry
  have h_det : s.val.val.det = (s.val.val.toSquareBlockProp (l ≤ floorOf ·)).det := by
    have h_tri : ∀ i, l ≤ floorOf i → ∀ j, ¬l ≤ floorOf j → s.val.val i j = 0 := fun i hi j hj ↦ by
      have h_entry : s.val.val i j = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) i j :=
        h i j (not_le.1 hj)
      rw [h_entry, one_apply_ne (fun h_eq ↦ by subst h_eq; exact hj hi)]
    rw [twoBlockTriangular_det' s.val.val (l ≤ floorOf ·) h_tri, outside, det_one, mul_one]
  have h_unitary : s.val.val.det ∈ unitary A := (U.det (H.isUnit.map detMonoidHom) s).property
  refine measurePreserving_mulVec _ ?_
  rw [← h_det]
  exact h_unitary.1

/-- The measure `η_l = heisenbergMeasure l` is carried by `N_l`. -/
lemma ae_mem_floorUnipotent [H : IsHermitianUnit T.splitGram] :
    ∀ᵐ x : T.G ∂heisenbergMeasure l, x ∈ floorUnipotent l := by
  fun_cases heisenbergMeasure
  · exact (ae_map_iff (by fun_prop) (measurableSet_floorGroup.inter
      (isClosed_of_entries_eq_one mem_unipotentBelow).measurableSet)).2
      (.of_forall (heisenbergElem_mem_floorUnipotent _))
  · simp

/-- The measure `η_l = heisenbergMeasure l` on the unitary group `T.G` is invariant under right and
under left translation by every element `s` of `N_l = floorUnipotent l = G_l ∩ N_(<l+1)`, that is,
`η_l ∗ δ_s = η_l` and `δ_s ∗ η_l = η_l`. For `l < ϱ`, `η_l` is the image of Haar measure on
`V_(l+1)` times the skew measure under the Heisenberg parametrisation of `N_l`; otherwise it is the
unit mass at `1`. -/
lemma heisenbergMeasure_mconv_dirac [H : IsHermitianUnit T.splitGram] (h : s ∈ floorUnipotent l) :
    heisenbergMeasure l ∗ₘ dirac s = heisenbergMeasure l ∧
    dirac s ∗ₘ heisenbergMeasure l = heisenbergMeasure l := by
  dsimp only [heisenbergMeasure]
  split_ifs with hl
  · obtain ⟨⟨v, t⟩, rfl⟩ := exists_eq_heisenbergElem_of_mem (a := ⟨l, hl⟩) h
    -- By `heisenbergElem_mul`, multiplication by `heisenbergElem a (v, t)` on either side
    -- translates the skew parameter, which `P.skewMeasure` absorbs, and translates the vector by
    -- `v`, which volume absorbs.
    have skew_inv (Φ : T.G → ℝ≥0∞) (w : {i : 𝔰.BesselIndex // l + 1 ≤ floorOf i} → A)
        (β₀ : skewAdjoint A) :
        ∫⁻ β, Φ (heisenbergElem ⟨l, hl⟩ (w, β + β₀)) ∂P.skewMeasure =
          ∫⁻ β, Φ (heisenbergElem ⟨l, hl⟩ (w, β)) ∂P.skewMeasure :=
      lintegral_add_right_eq_self (fun β ↦ Φ (heisenbergElem ⟨l, hl⟩ (w, β))) β₀
    have vec_inv (Φ : T.G → ℝ≥0∞) :
        ∫⁻ w, ∫⁻ β, Φ (heisenbergElem ⟨l, hl⟩ (w + v, β)) ∂P.skewMeasure =
          ∫⁻ w, ∫⁻ β, Φ (heisenbergElem ⟨l, hl⟩ (w, β)) ∂P.skewMeasure :=
      lintegral_add_right_eq_self (fun w ↦ ∫⁻ β, Φ (heisenbergElem ⟨l, hl⟩ (w, β)) ∂P.skewMeasure) v
    have h_meas_heis : Measurable (heisenbergElem (T := T) ⟨l, hl⟩) :=
      continuous_heisenbergElem.measurable
    constructor
    · refine ext_of_lintegral _ fun Φ hΦ ↦ ?_
      have hΦr : Measurable fun x : T.G ↦ Φ (x * heisenbergElem ⟨l, hl⟩ (v, t)) :=
        hΦ.comp (measurable_mul_const _)
      rw [mconv_dirac, lintegral_map hΦ (measurable_mul_const _),
        lintegral_map hΦr h_meas_heis, lintegral_map hΦ h_meas_heis,
        lintegral_prod (f := fun a ↦ Φ (heisenbergElem ⟨l, hl⟩ a * heisenbergElem ⟨l, hl⟩ (v, t)))
          (hΦr.comp h_meas_heis).aemeasurable,
        lintegral_prod (f := fun a ↦ Φ (heisenbergElem ⟨l, hl⟩ a))
          (hΦ.comp h_meas_heis).aemeasurable]
      simp only [heisenbergElem_mul, add_assoc]
      simp_rw [skew_inv, vec_inv]
    · refine ext_of_lintegral _ fun Φ hΦ ↦ ?_
      have hΦl : Measurable fun x : T.G ↦ Φ (heisenbergElem ⟨l, hl⟩ (v, t) * x) :=
        hΦ.comp (measurable_const_mul _)
      rw [dirac_mconv, lintegral_map hΦ (measurable_const_mul _),
        lintegral_map hΦl h_meas_heis, lintegral_map hΦ h_meas_heis,
        lintegral_prod (f := fun a ↦ Φ (heisenbergElem ⟨l, hl⟩ (v, t) * heisenbergElem ⟨l, hl⟩ a))
          (hΦl.comp h_meas_heis).aemeasurable,
        lintegral_prod (f := fun a ↦ Φ (heisenbergElem ⟨l, hl⟩ a))
          (hΦ.comp h_meas_heis).aemeasurable]
      simp only [heisenbergElem_mul, add_comm t, add_comm v, add_assoc]
      simp_rw [skew_inv, vec_inv]
  · simp [eq_one_of_mem_floorGroup_inf h (Or.inr (not_lt.1 hl))]

/-- Let `η_l = heisenbergMeasure l` be the measure on the unitary group `T.G` carried by the
Heisenberg group `N_l`. For `l < ϱ` it is the image of Haar measure on `V_(l+1)` times the skew
measure of the place under `heisenbergElem`, and otherwise it is the unit mass at `1`. If `s` lies
in `G_(l+1) = floorGroup (l + 1)`, the unitary elements fixing every basis vector of floor below
`l + 1`, then `dirac s ∗ₘ η_l = η_l ∗ₘ dirac s`. -/
lemma dirac_mconv_heisenbergMeasure_comm [H : IsHermitianUnit T.splitGram]
    (h : s ∈ floorGroup (l + 1)) :
    dirac s ∗ₘ heisenbergMeasure l = heisenbergMeasure l ∗ₘ dirac s := by
  dsimp only [heisenbergMeasure]
  split_ifs with hl
  · -- by `mul_heisenbergElem`, moving `s` across applies its block to the vector, which keeps the
    -- volume
    have h_meas_heis : Measurable (heisenbergElem (T := T) ⟨l, hl⟩) :=
      continuous_heisenbergElem.measurable
    have h_mp := (measurePreserving_floor_block_mulVec h).prod (.id P.skewMeasure)
    rw [dirac_mconv, mconv_dirac, Measure.map_map (measurable_const_mul s) h_meas_heis,
      Measure.map_map (measurable_mul_const s) h_meas_heis]
    nth_rw 2 [← h_mp.map_eq]
    rw [Measure.map_map ((measurable_mul_const s).comp h_meas_heis) h_mp.measurable]
    congr 1
    funext x
    exact mul_heisenbergElem (a := ⟨l, hl⟩) h
  · simp

/-! ### Convolutions along the floors, quadric measures and Plancherel -/

/-- For measures σ_l on the unitary group, the convolution σ_{a+i−1} ∗ ⋯ ∗ σ_a in descending order
of i consecutive terms; the Dirac measure at 1 if i = 0. -/
def descConv : ℕ → ℕ → Measure T.G
  | _, 0 => dirac 1
  | a, i + 1 => descConv (a + 1) i ∗ₘ σ a

/-- For measures σ_l on the unitary group, the convolution σ_0 ∗ ⋯ ∗ σ_{j−1} in ascending order; the
Dirac measure at 1 if j = 0. -/
def ascConv : ℕ → Measure T.G
  | 0 => dirac 1
  | j + 1 => ascConv j ∗ₘ σ j

instance (a i : ℕ) : SFinite (descConv σ a i) := by
  induction i generalizing a with
  | zero => dsimp only [descConv]; infer_instance
  | succ i ih => dsimp only [descConv]; infer_instance

instance : SFinite (ascConv σ j) := by
  induction j with
  | zero => dsimp only [ascConv]; infer_instance
  | succ j ih => dsimp only [ascConv]; infer_instance

variable {σ}

lemma lintegral_mconv_dirac (f : T.G → ℝ≥0∞) :
    lintegral (μ ∗ₘ dirac s) f = ∫⁻ x : T.G, f (x * s) ∂μ := by
  simpa [↓ mconv_dirac] using lintegral_map_equiv f (.mulRight s)

lemma lintegral_dirac_mconv (f : T.G → ℝ≥0∞) (s : T.G) :
    lintegral (dirac s ∗ₘ μ) f = ∫⁻ x : T.G, f (s * x) ∂μ := by
  simpa [↓ dirac_mconv] using lintegral_map_equiv f (.mulLeft s)

/-- If `dirac s ∗ₘ μ = μ ∗ₘ dirac t`, then the substitution `x ↦ s⁻¹ * x * t` preserves integrals
against `μ`. -/
lemma lintegral_eq_of_dirac_mconv_eq {t : T.G} (h : dirac s ∗ₘ μ = μ ∗ₘ dirac t) :
    lintegral μ f = ∫⁻ x : T.G, f (s⁻¹ * x * t) ∂μ := by
  simpa [↓lintegral_dirac_mconv, ↓lintegral_mconv_dirac, mul_assoc] using
    congrArg (lintegral · fun x : T.G ↦ f (s⁻¹ * x)) h

/-- The integral against a convolution as an iterated integral, with the right factor outside. -/
lemma lintegral_mconv_symm (hf : Measurable f) :
    lintegral (μ ∗ₘ ν) f = ∫⁻ y : T.G, ∫⁻ x : T.G, f (x * y) ∂μ ∂ν :=
  (lintegral_mconv hf).trans (lintegral_lintegral_swap (by fun_prop))

/-- The mass of `Y` under `μ ∗ₘ ν` is the `ν`-integral of the mass of `Y * y⁻¹` under `μ`. -/
lemma mconv_apply_eq_lintegral {Y : Set T.G} (hY : MeasurableSet Y) :
    (μ ∗ₘ ν) Y = ∫⁻ y : T.G, μ {x : T.G | x * y ∈ Y} ∂ν :=
  (map_apply measurable_mul hY).trans (prod_apply_symm (measurable_mul hY))

omit [SFinite μ] in
/-- The convolution of two measures carried by a measurable subgroup `S` is carried by `S`. -/
lemma ae_mem_mconv (hμ : ∀ᵐ x : T.G ∂μ, x ∈ S) (hν : ∀ᵐ x : T.G ∂ν, x ∈ S)
    (hS : MeasurableSet (S : Set T.G) := by exact measurableSet_floorGroup) :
    ∀ᵐ x : T.G ∂μ ∗ₘ ν, x ∈ S :=
  (ae_map_iff (by fun_prop) hS).2
    (.mono (measure_prod_compl_eq_zero hμ hν) fun _ hx ↦ S.mul_mem hx.1 hx.2)

/-- If `dirac s` commutes with `ν` for `μ`-almost every `s`, then `μ` commutes with `ν` under
convolution. -/
lemma mconv_comm_of_ae (h : ∀ᵐ s : T.G ∂μ, dirac s ∗ₘ ν = ν ∗ₘ dirac s) : μ ∗ₘ ν = ν ∗ₘ μ := by
  refine ext_of_lintegral _ fun f hf ↦ ?_
  calc lintegral (μ ∗ₘ ν) f = ∫⁻ s, ∫⁻ y, f (s * y) ∂ν ∂μ := lintegral_mconv hf
    _ = ∫⁻ s, ∫⁻ y, f (y * s) ∂ν ∂μ :=
      lintegral_congr_of_ae_imp h fun s hs ↦ by
        rw [← lintegral_dirac_mconv, hs, lintegral_mconv_dirac]
    _ = lintegral (ν ∗ₘ μ) f := (lintegral_mconv_symm hf).symm

/-- A descending convolution of `i + j` terms splits after the first `i` indices. -/
lemma descConv_add (i j a : ℕ) :
    descConv σ a (i + j) = descConv σ (a + i) j ∗ₘ descConv σ a i := by
  induction i generalizing a with
  | zero => simp [descConv]
  | succ i ih =>
    rw [show i + 1 + j = i + j + 1 by ring, descConv, ih, mconv_assoc,
      show a + 1 + i = a + (i + 1) by ring, descConv]

/-- A descending convolution starting at `0` gains its next term `σ i` on the left. -/
lemma descConv_succ (i : ℕ) : descConv σ 0 (i + 1) = σ i ∗ₘ descConv σ 0 i := by
  simp [↓descConv_add, descConv]

omit [TopologicalSpace A] [Place A] [SFinite μ] in
/-- A function with nonzero integral is nonzero at some point where a given almost everywhere
property holds. -/
lemma exists_ne_zero_of_ae {p : T.G → Prop} (h : ∀ᵐ x : T.G ∂μ, p x) (hf : lintegral μ f ≠ 0) :
    ∃ x : T.G, p x ∧ f x ≠ 0 := by
  by_contra! h_zero
  exact hf (lintegral_eq_zero_of_ae_eq_zero (h.mono h_zero))

/-- The measure on a quadric in V_b: the image of `New.Floors.Place.quadricMeasure` with parameter β
under the basis `F.floorBasis b`. By default, β is obtained from h(f_b, f_b) by `skewUnitMul`. -/
abbrev HyperbolicBasis.floorQuadricMeasure [_H : IsHermitianUnit T.splitGram]
    (β : skewAdjoint A := skewUnitMul (T.splitGram (𝔰.besselFrame b) (𝔰.besselFrame b))
      (IsHermitian.apply IsHermitianUnit.conjTranspose_eq (𝔰.besselFrame b) (𝔰.besselFrame b))) :
    Measure (𝔰.BesselIndex → A) :=
  (quadricMeasure (hyperbolicGram (FloorPairs b m) 1) β).map (F.floorBasis b *ᵥ ·)

/-- Let `V_b` be the span of the basis vectors of floor at least `b`, with Haar measure
`floorVolume b` (the volume on those coordinates, extended by zero). The measures
`F.floorQuadricMeasure b β`, images under the basis `F.floorBasis b` of the quadric measures with
skew parameter `β`, disintegrate this Haar measure along `h(x, x)`, where `h = T.splitGram`. -/
lemma HyperbolicBasis.isDisintegration_floorVolume [H : IsHermitianUnit T.splitGram]
    {μ : Measure (𝔰.BesselIndex → A)} (hμ : μ = FloorGroups.floorVolume b) :
    IsDisintegration μ T.splitGram (F.floorQuadricMeasure b ·) := by
  -- Transport `isDisintegration_quadricMeasure` along `F.floorBasis b`. Its Gram matrix has square
  -- one, which gives a left inverse of `F.floorBasis b`.
  have gram : (F.floorBasis b)ᴴ * T.splitGram * F.floorBasis b =
      planeSumGram (hyperbolicGram (FloorPairs b m) (1 : Matrix ι ι A)) := F.gram_floorBasis b
  have left_inv :
      (F.floorBasis b)ᴴ * T.splitGram * F.floorBasis b * ((F.floorBasis b)ᴴ * T.splitGram) *
        F.floorBasis b = 1 := by
    rw [Matrix.mul_assoc _ _ (F.floorBasis b), gram, planeSumGram_hyperbolicGram_sq]
  rw [hμ, ← F.map_floorBasis_volume b]
  exact (isDisintegration_quadricMeasure (by simp [fromBlocks_conjTranspose,
    conjTranspose_fromRows_eq_fromCols_conjTranspose,
    conjTranspose_fromCols_eq_fromRows_conjTranspose])).map gram left_inv

/-- Let `b ≤ ϱ` and let `Z` be a nonempty standard Borel space. Let `Φ : T.G → Z` be a measurable
function that is left invariant under `Q_(b+1) ∩ G_b`, where `Q_(b+1)` is the partially
unitriangular group `partialUnitriangularGroup (b + 1)` and `G_b = floorGroup b` is the group of
isometries fixing every basis vector of floor below `b`. Then there is a measurable `Ψ` on vectors
with `Φ σ = Ψ (orbitPoint b σ)` for every `σ ∈ G_b`, where `orbitPoint b σ = σ⁻¹ f_b` and `f_b` is
the vector of index `b` in the frame `(e_0, …, e_{ϱ-1}, z)`. -/
lemma exists_factor_orbitPoint [StandardBorelSpace Z] [Nonempty Z] {Φ : T.G → Z} (hΦ : Measurable Φ)
    (h_inv : (partialUnitriangularGroup (b + 1) ⊓ floorGroup b).FixesLeft Φ) :
    ∃ Ψ : (𝔰.BesselIndex → A) → Z, Measurable Ψ ∧ ∀ σ ∈ floorGroup b, Φ σ = Ψ (orbitPoint b σ) := by
  -- On `floorGroup b` the invariant function `Φ` factors through `orbitPoint b`, as
  -- `Ψ ∘ orbitPoint b`. The source is standard Borel and the range of `orbitPoint b` is countably
  -- separated, so `Ψ` is measurable on that range; it extends measurably to all vectors because `Z`
  -- is standard Borel and nonempty.
  have : StandardBorelSpace (T.floorGroup b) := measurableSet_floorGroup.standardBorel
  have h_factors : FactorsThrough (Φ ∘ (↑)) fun σ : T.floorGroup b ↦ orbitPoint b σ.val :=
    fun σ τ h ↦ by simpa using h_inv _ (inv_mul_mem_of_orbitPoint_eq σ⁻¹.property τ⁻¹.property h) τ
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (𝔰.BesselIndex → A) → Z,
      Φ ∘ (↑) = Ψ ∘ fun σ : T.floorGroup b ↦ orbitPoint b σ.val :=
    (factorsThrough_iff _).1 h_factors
  have h_meas : Measurable (Ψ ∘ fun σ : T.floorGroup b ↦ orbitPoint b σ.val) := by
    rw [← hΨ]
    exact hΦ.comp (by fun_prop)
  rw [Measurable.measurable_comp_iff_restrict (by fun_prop)] at h_meas
  obtain ⟨Ψ', hΨ'_meas, hΨ'⟩ := h_meas.exists_eq_measurable_comp
  refine ⟨Ψ', hΨ'_meas, fun σ hσ ↦ ?_⟩
  calc Φ σ = Ψ (orbitPoint b σ) := congrFun hΨ ⟨σ, hσ⟩
    _ = Ψ' (orbitPoint b σ) := congrFun hΨ' ⟨orbitPoint b σ, ⟨σ, hσ⟩, rfl⟩

/-- If every `σ l` is carried by `G_l`, then so is the descending convolution starting at `l`. -/
lemma ae_descConv_mem (h : ∀ {l : ℕ}, ∀ᵐ x : T.G ∂σ l, x ∈ floorGroup l) :
    ∀ᵐ x : T.G ∂descConv σ l i, x ∈ floorGroup l := by
  induction i generalizing l with
  | zero => simp [descConv]
  | succ i ih =>
    exact ae_mem_mconv (ih.mono (floorGroup_anti l.le_succ)) h measurableSet_floorGroup

variable [H : IsHermitianUnit T.splitGram]

/-- Let `η_i = heisenbergMeasure i` be the measure on the unitary group `T.G` carried by the
Heisenberg group `N_i`: the image of Haar measure on `V_(i+1)` times the skew measure of the place
for `i < ϱ`, and the unit mass at `1` otherwise. Let `η_{<j} = ascConv heisenbergMeasure j` be the
convolution `η₀ ∗ ⋯ ∗ η_{j−1}`, which is the Dirac mass at `1` if `j = 0`. For every `s` in
`G_j = T.floorGroup j`, the unitary elements fixing every basis vector of floor below `j`, the Dirac
mass at `s` commutes with `η_{<j}` under convolution. -/
lemma ascConv_heisenbergMeasure_dirac_comm :
    ∀ s ∈ T.floorGroup j,
      dirac s ∗ₘ ascConv heisenbergMeasure j = ascConv heisenbergMeasure j ∗ₘ dirac s := by
  induction j with
  | zero => simp [ascConv]
  | succ j ih =>
    intro s hs
    rw [ascConv, ← mconv_assoc, ih s (floorGroup_anti j.le_succ hs), mconv_assoc,
      dirac_mconv_heisenbergMeasure_comm hs, mconv_assoc]

/-- η_{<j+1} = η_j ∗ η_{<j}: the last factor may be moved to the front, as η_j is carried by G_j. -/
lemma ascConv_heisenbergMeasure_succ :
    (ascConv heisenbergMeasure (j + 1) : Measure T.G) =
      heisenbergMeasure j ∗ₘ ascConv heisenbergMeasure j :=
  (mconv_comm_of_ae
    (ae_mem_floorUnipotent.mono fun x hx ↦ ascConv_heisenbergMeasure_dirac_comm x hx.1)).symm

/-- Let `A` be a place and `T` a middle Gram matrix whose split Gram matrix `T.splitGram` is
hermitian and invertible. In the unitary group of `T.splitGram`, let η_{<j} = η₀ ∗ ⋯ ∗ η_{j−1} be
the ascending convolution of the Heisenberg measures. Here η_l is the image of Haar measure on
V_(l+1) times the skew measure under the parametrisation of N_l for l < ϱ, and the unit mass at 1
otherwise. Then η_{<j} ∗ δ_s = η_{<j} and δ_s ∗ η_{<j} = η_{<j} for every s in N_(<j), the group of
elements that are unitriangular when basis vectors of floor below j keep their level and all others
get the middle level. -/
lemma ascConv_heisenbergMeasure_invariant (hs : s ∈ unipotentBelow j) :
    ascConv heisenbergMeasure j ∗ₘ dirac s = ascConv heisenbergMeasure j ∧
    dirac s ∗ₘ ascConv heisenbergMeasure j = ascConv heisenbergMeasure j := by
  refine unipotentBelow_induction
    (C := fun (i : ℕ) (x : T.G) ↦
      ascConv heisenbergMeasure i ∗ₘ dirac x = ascConv heisenbergMeasure i ∧
      dirac x ∗ₘ ascConv heisenbergMeasure i = ascConv heisenbergMeasure i)
    ?_ ?_ j s hs
  · simp
  · -- `heisenbergMeasure j` absorbs `γ` and `ascConv heisenbergMeasure j` absorbs `ν`; the two
    -- measures commute
    intro j γ hγ ν ⟨asc_ν, ν_asc⟩
    obtain ⟨η_γ, γ_η⟩ := heisenbergMeasure_mconv_dirac hγ
    rw [← dirac_mconv_dirac]
    constructor
    · rw [← mconv_assoc, ascConv, mconv_assoc _ (heisenbergMeasure j), η_γ, ← ascConv,
        ascConv_heisenbergMeasure_succ, mconv_assoc, asc_ν]
    · rw [mconv_assoc, ascConv, ← mconv_assoc (dirac ν), ν_asc, ← ascConv,
        ascConv_heisenbergMeasure_succ, ← mconv_assoc, γ_η]

/-- The measure η_{<j} = η₀ ∗ ⋯ ∗ η_{j−1} is carried by `N_(<j)`. -/
lemma ae_ascConv_mem_unipotentBelow :
    ∀ᵐ x : T.G ∂ascConv heisenbergMeasure j, x ∈ T.unipotentBelow j := by
  induction j with
  | zero => simp [ascConv]
  | succ j ih =>
    exact ae_mem_mconv (ih.mono fun _ hx ↦ unipotentBelow_le_succ hx)
      (ae_mem_floorUnipotent.mono fun _ hx ↦ hx.2)
      (isClosed_of_entries_eq_one mem_unipotentBelow).measurableSet

omit [DecidableEq ι] in
/-- Plancherel's inequality with a damping factor `∏ i, G (v i)`, for `G ≥ 0` continuous and
integrable and the additive character `ψ` of the place `A`: the constant is the `L¹` norm of the
transform of `G` (dilated by `ξ`), to the power `card ι`. -/
lemma Place.lintegral_damped_fourier_le (ξ : A) {G : A → ℝ} (hG : Continuous G)
    (hG_int : Integrable G) (hG_pos : 0 ≤ G) {f : (ι → A) → ℂ} (hf : Integrable f)
    (hf_meas : Measurable f) :
    ∫⁻ v : ι → A, ‖(‖∫ w : ι → A, P.ψ (ξ * star v ⬝ᵥ w) * f w‖ ^ 2 * ∏ i : ι, G (v i) : ℂ)‖ₑ ≤
      (∫⁻ a : A, ‖∫ v : A, G v * P.ψ (star v * ξ * a)‖ₑ) ^ card ι * ∫⁻ w : ι → A, ‖f w‖ₑ ^ 2 := by
  -- Expand the square as a double integral over `x = (w, w')` and integrate over `v` first.
  let g (v : ι → A) (x : (ι → A) × (ι → A)) : ℂ :=
    P.ψ (ξ * star v ⬝ᵥ (x.2 - x.1)) * ((∏ i, G (v i)) * (star (f x.1) * f x.2))
  have hg : Integrable g.uncurry :=
    .mono ((Integrable.fintype_prod fun _ ↦ hG_int).smul_prod (hf.mul_prod hf))
      (Measurable.aestronglyMeasurable (by fun_prop)) (by simp [g, uncurry])
  have h_expand (v : ι → A) :
      ‖∫ w : ι → A, P.ψ (ξ * star v ⬝ᵥ w) * f w‖ ^ 2 * ∏ i : ι, (G (v i) : ℂ) =
        ∫ x : (ι → A) × (ι → A), g v x := by
    rw [← Complex.conj_mul', ← integral_conj, ← integral_prod_mul, ← integral_mul_const]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp [g, mul_sub, P.ψ.map_sub_eq_div, division_def, Complex.inv_eq_conj]
    ring
  -- The transform of the damping factor is a product of transforms of `G`.
  have h_factor (z : ι → A) : ‖∫ v : ι → A, P.ψ (ξ * star v ⬝ᵥ z) * ∏ i : ι, (G (v i) : ℂ)‖ₑ ≤
      ∏ i : ι, ‖∫ v : A, G v * P.ψ (star v * ξ * z i)‖ₑ := by
    have h_eq : (∫ v : ι → A, P.ψ (ξ * star v ⬝ᵥ z) * ∏ i : ι, (G (v i) : ℂ)) =
        ∏ i : ι, ∫ v : A, (G v : ℂ) * P.ψ (star v * ξ * z i) := by
      rw [← integral_fintype_prod_volume_eq_prod]
      congr 1; funext v
      rw [dotProduct, Finset.mul_sum, AddChar.map_sum_eq_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [mul_comm, Pi.star_apply, ← mul_assoc, mul_comm ξ]
    rw [h_eq]
    simp only [eNorm, ← ofNNReal_finsetProd, ← nnNorm_prod, le_rfl]
  -- For a fixed difference `z = w' - w`, Cauchy–Schwarz bounds `∫ |f w| |f (w + z)|`.
  have h_cauchy (z : ι → A) :
      ∫⁻ w : ι → A, ‖f w‖ₑ * ‖f (w + z)‖ₑ ≤ ∫⁻ w : ι → A, ‖f w‖ₑ ^ 2 := by
    simpa [← rpow_add_of_nonneg, ← two_mul, lintegral_add_right_eq_self (‖f ·‖ₑ ^ 2)] using
      lintegral_mul_le_Lp_mul_Lq _ .two_two hf.1.eNorm (hf.comp_add_right z).1.eNorm
  have h_diff (z : ι → A) : ∫⁻ w : ι → A, ‖∫ v : ι → A, g v (w, w + z)‖ₑ ≤
      (∏ i : ι, ‖∫ v : A, G v * P.ψ (star v * ξ * z i)‖ₑ) * ∫⁻ w : ι → A, ‖f w‖ₑ ^ 2 := by
    simpa [g, ← mul_assoc (ψ _), integral_mul_const, lintegral_const_mul'] using
      mul_le_mul' (h_factor z) (h_cauchy z)
  have h_nonneg (v : ι → A) :
      (‖∫ x : (ι → A) × (ι → A), g v x‖ : ℂ) = ∫ x : (ι → A) × (ι → A), g v x := by
    simp [← h_expand, abs_of_nonneg (hG_pos _)]
  simp only [Complex.ofReal_prod, h_expand]
  calc ∫⁻ v, ‖∫ x, g v x‖ₑ
    _ ≤ ‖∫ v, ∫ x, g v x‖ₑ := by
      -- The inner integrals are non-negative reals.
      grw [← ofReal_integral_norm_eq_lintegral_eNorm (by exact hg.integral_prod_left),
        Real.ofReal_le_eNorm]
      rw [← integral_congr_ae (.of_forall h_nonneg), integral_complex_ofReal]
      simp [eNorm]
    _ ≤ ∫⁻ x : (ι → A) × (ι → A), ‖∫ v, g v x‖ₑ := by
      grw [integral_integral_swap hg, eNorm_integral_le_lintegral_eNorm]
    _ ≤ ∫⁻ z : ι → A, ∫⁻ w, ‖∫ v, g v (w, w + z)‖ₑ := by
      grw [volume_eq_prod, ← (measurePreserving_prod_add_swap ..).map_eq, lintegral_map_le,
        lintegral_prod_le]
      fun_prop
    _ ≤ ∫⁻ z : ι → A, (∏ i, ‖∫ v, G v * P.ψ (star v * ξ * z i)‖ₑ) * ∫⁻ w, ‖f w‖ₑ ^ 2 :=
      lintegral_mono h_diff
    _ = (∫⁻ a : A, ‖∫ v : A, G v * P.ψ (star v * ξ * a)‖ₑ) ^ card ι *
          ∫⁻ w : ι → A, ‖f w‖ₑ ^ 2 := by
      have h_meas_hat : Measurable fun a : A ↦ ‖∫ v : A, (G v : ℂ) * P.ψ (star v * ξ * a)‖ₑ := by
        fun_prop
      have h_meas_prod : Measurable fun z : ι → A ↦
          ∏ i : ι, ‖∫ v : A, (G v : ℂ) * P.ψ (star v * ξ * z i)‖ₑ :=
        Finset.measurable_prod _ fun i _ ↦ h_meas_hat.comp (measurable_pi_apply i)
      rw [lintegral_mul_const _ h_meas_prod, card, ← Finset.prod_const (lintegral ..),
        ← TauCeti.lintegral_fintype_prod_eq_prod _ (fun _ ↦ h_meas_hat), volume_pi]
/-- Plancherel's inequality at a place A: for a unit η and f measurable and integrable on A^ι,
∫ |∫ ψ(η v*w) f(w) dw|² dv ≤ (c/md η)^{|ι|} ∫ |f|². Here v*w is `star v ⬝ᵥ w`, ψ is the additive
character of the place, and md is its `modulus`. The constant c = `kernelBound` is part of the data
of the place: a bound in [0, ∞] on the L¹ norm of the Fourier transform of a kernel that the place
provides. -/
lemma Place.plancherel_inequality (η : Aˣ) {f : (ι → A) → ℂ} (hf : Integrable f)
    (hf_meas : Measurable f) :
    ∫⁻ v : ι → A, ‖∫ w : ι → A, P.ψ (η * star v ⬝ᵥ w) * f w‖ₑ ^ 2 ≤
      (P.kernelBound / P.modulus η) ^ card ι * ∫⁻ w : ι → A, ‖f w‖ₑ ^ 2 := by
  -- Damp the integrand by `∏ i, G (star x * v i)`, which tends to `1` as `x → 0`. By Fatou's lemma
  -- it suffices to bound the damped integral for units `x`, which accumulate at `0`.
  obtain ⟨G, hG, hG_int, hG_pos, hG_zero, hG_mass⟩ := P.exists_plancherel_kernel
  let damped (x : A) (v : ι → A) : ℝ≥0∞ :=
    ‖(‖∫ w, P.ψ (η * star v ⬝ᵥ w) * f w‖ ^ 2 * ∏ i, G (star x * v i) : ℂ)‖ₑ
  have h_meas_damped (x : A) : Measurable (damped x) := by
    dsimp only [damped]
    fun_prop
  have h_meas_hat : Measurable fun a : A ↦ ‖∫ v : A, (G v : ℂ) * P.ψ (star v * a)‖ₑ := by
    fun_prop
  have h_limit (v : ι → A) :
      Tendsto (damped · v) (nhds 0) (nhds (‖∫ w, P.ψ (η * star v ⬝ᵥ w) * f w‖ₑ ^ 2)) :=
    Continuous.tendsto' (by fun_prop) 0 _ (by simp [damped, eNorm, hG_zero])
  have h_unit (u : Aˣ) : ∫⁻ v : ι → A, damped u v ≤
      (P.kernelBound / P.modulus η) ^ card ι * ∫⁻ w : ι → A, ‖f w‖ₑ ^ 2 := by
    -- Substitute `v ↦ (star u)⁻¹ • v` on the left and `z ↦ η * u⁻¹ * z` in the mass of the kernel;
    -- both sides acquire the factor `(modulus u)⁻¹ ^ card ι`.
    have h_det_unit : IsUnit ((star u⁻¹.1 • (1 : Matrix ι ι A)).det) := by
      rw [det_smul, det_one, mul_one]; exact u⁻¹.isUnit.star.pow _
    have h_scale_meas : Measurable ((star u⁻¹.1 • (1 : Matrix ι ι A)) *ᵥ ·) := by fun_prop
    grw [lintegral_eq_mul_lintegral_map (map_mulVec_volume _ (star u⁻¹.1 • 1) h_det_unit)
          (modulus_ne_zero h_det_unit.unit) (modulus_ne_top h_det_unit.unit),
        lintegral_map_le (damped u) h_scale_meas.aemeasurable,
        ← hG_mass,
        lintegral_eq_mul_lintegral_map (map_mul_volume (η * u⁻¹)) (modulus_ne_zero _)
          (modulus_ne_top _),
        lintegral_map h_meas_hat (measurable_const_mul _)]
    have h_cancel (a : A) : star u.val * (star u⁻¹.val * a) = a := by simp [← mul_assoc, ← star_mul]
    simpa [damped, smul_mulVec, mul_pow, ENNReal.mul_div_right_comm, ENNReal.div_self,
      mul_assoc, h_cancel] using
      mul_le_mul_right (lintegral_damped_fourier_le (η.val * u⁻¹.val) hG hG_int hG_pos hf hf_meas)
        ((P.modulus u)⁻¹ ^ card ι)
  grw [lintegral_mono fun v ↦ (h_limit v).liminf_eq.ge, lintegral_liminf_le h_meas_damped]
  exact liminf_le_of_frequently_le'
    ((mem_closure_iff_frequently.1 (dense_of_ae ae_isUnit 0)).mono (Set.forall_mem_range.2 h_unit))

end New.Floors

end
