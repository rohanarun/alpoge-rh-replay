module

public import Lib.Weil.DualPair.TwoEdges
public import Lib.Weil.MixedModel.AdaptedSplitting
public import Lib.Weil.Periods.ConstantTerm
public import New.UpperBound.Objects.Rows

/-!
# Finite zero terms and the evaluation of pairs of edges in the tower of spaces `Y_k`

For a splitting `D` of a hermitian space `V`, the zero term `D.zeroTerm` along its isotropic frame
is split into a real and a finite part, `New.Seesaw.zeroTermFin D`. For spaces presented by
`New.Grading` as a definite part plus a string of basis vectors, the part of grade zero gives
splittings. On `V⁻ ⊕ V''` this leads to a splitting down to `Hom (X', X⁻ ⊕ X'')` and an evaluation
of finite data, and both are equivariant for `New.Seesaw.tripleWeil`. This evaluation is then
applied to the tower `New.Data.spaceY k`, `k ≤ m = 2 ϱ + 2`, two lifts at a time; here `m` and `ϱ`
are the natural numbers `New.Data.m` and `New.Data.ϱ`.

## Main definitions and results

Throughout, a *string* of a grading is the block of basis vectors outside the definite part, and
`DoubleLiftData` records two successive steps `Y → Y' → Y''` where the first step makes the string
one shorter and the second, unless the string is already empty, makes it shorter by one.

* `New.Seesaw.zeroTermFin`: the finite part of the zero term. It obeys the law of the zero term for
  finite points of the parabolic subgroup (`New.Seesaw.zeroTermFin_omega`) and is not zero at the
  vacuum (`New.Seesaw.zeroTermFin_vacElem_ne_zero`).
* `New.Seesaw.GradeZeroPart`, `New.Seesaw.GradeZeroPart.splitting`: the part of grade zero, and the
  splitting it gives.
* `New.Seesaw.DoubleLiftData`: the part of grade zero of `V⁻ ⊕ V''` is `X⁻ ⊕ X''` plus hyperbolic
  planes. `New.Seesaw.middleDoubleLift` (one plane) and `New.Seesaw.lastDoubleLift` (none) are the
  two instances.
* `New.Seesaw.DoubleLiftData.splitting`, `New.Seesaw.DoubleLiftData.finEval`: the splitting down to
  `Hom (X', X⁻ ⊕ X'')` and the evaluation of finite data.
  `New.Seesaw.DoubleLiftData.zeroTerm_splitting_tripleWeil` and
  `New.Seesaw.DoubleLiftData.finEval_arrowProduct_equivariant` show that both are equivariant.
* `New.Data.doubleLiftEvalY`: the evaluation of the pair `Y_{2i} → Y_{2i+1} → Y_{2i+2}`, by
  `New.Seesaw.middleDoubleLift` for `i < ϱ` and `New.Seesaw.lastDoubleLift` for `i = ϱ`.
* `New.Data.translatedPointDatumY`, `New.Data.evaluatedDatum`: the data `New.Data.pointDatumY` moved
  by finite adelic points of the unitary groups, and their evaluation.

Notions from other files:
* `New.Space E n s`: a hermitian space with a point, given by a matrix `J` over `E` and `x` in
  `GL_n(𝔸)` with `xᴴ J x` equal to `diag s` at the infinite places and `1` at the finite places.
  `𝒮 V` is its space of data, with the Weil operators `V.ω g` and the Heisenberg operators `V.ϱ y`.
* `New.Space.Splitting`: dual isotropic frames `l`, `k` with columns indexed by `p` and an isometry
  `i : V₀ → V` onto their orthogonal complement.
* `New.Space.Splitting.zeroTerm`: the bounded map `𝒮 V → 𝒮 V₀` that sends `f` to the function whose
  value at `y` is the mean of `f (i y + k b)` over `b` in `𝔸 ^ p` modulo `E ^ p`.
* `New.Space.finHeisenbergOp`: the Heisenberg operator of a finite adelic vector `x` on `𝒮 V`; it
  translates by `α x`, with `α` the finite idele of `New.WeilData`.
* `New.Data.spaceY`: the hermitian space `Y_k` with its adelic frame, chosen as in
  `New.Data.exists_space_isStd_of_le_and_gram_eq_of_lt`.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work. See `Lib.Weil.MixedModel.ZeroTerm` for
sources.
-/

@[expose] public section

noncomputable section

namespace New.Seesaw

/-!
## The finite part of the zero term and the support of its translates

* `New.Seesaw.zeroTermFin_mem_finitePart`, `New.Seesaw.exists_zeroTerm_rho_integrated_eq`:
  `zeroTermFin D` preserves the finite parts and computes `D.zeroTerm` on pure tensors.
* `New.Seesaw.exists_zeroTermFin_finHeisenbergOp_add`: its values on the finite translates of the
  vacuum.
* `New.Seesaw.mem_zeroTermLattice_iff_selfDualAddChar`,
  `New.Seesaw.exists_zeroTermFin_vacElem_eq_sum`: the lattice `New.Seesaw.zeroTermLattice D` is
  unimodular, and the value at the vacuum is a multiple of a sum of translates of the vacuum by
  vectors of this lattice.

`V.integrated v f` is the tensor of a real Fock vector `v` with `f`, `V.finHeisenbergOp x` the
Heisenberg operator of a finite adelic vector `x`, `V.finitePart` the span of the
`V.finHeisenbergOp x`-translates of the vacuum, and `New.stdLattice` the standard lattice `Ô ^ n`.
-/

section FiniteZeroTerm

open Matrix Prod Space Splitting stdLattice Fock

variable {E n n₀ p : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] [Fintype n₀]
  [DecidableEq n₀] [Fintype p] [DecidableEq p] {s : n → ℤˣ} {s₀ : n₀ → ℤˣ} {V : Space E n s}
  {V₀ : Space E n₀ s₀} [WeilData E]

/-- The finite part of the zero term along the splitting `D` of `V` over `V₀`. It is the map
`f ↦ D.zeroTerm (v ⊗ f)`, where `⊗` is `V.integrated` and `v` is the Fock vacuum moved by the real
part of a chosen point `g` of the unitary group with `D.IsAdapted g 1` (the frame of `D` moved by
`g⁻¹` is orthonormal at the infinite places and integral at the finite places). -/
@[local simp]
noncomputable def zeroTermFin (D : V.Splitting V₀ p) : 𝒮 V →L[ℂ] 𝒮 V₀ :=
  D.zeroTerm ∘L
    V.integrated (realWeil (blockU (D.exists_isAdapted_and_frame_eq 1).choose.1) Fock.vacVector)

/-- With `g` the adapted point chosen in the definition, `zeroTermFin D` undoes the finite part
`g.2` of `g`, projects on the real vacuum (`V.projReal`), applies the Weil operator `V.ω g` and
takes the zero term. -/
lemma zeroTermFin_eq (D : V.Splitting V₀ p) {g : G E s}
    (hg : g = (D.exists_isAdapted_and_frame_eq 1).choose) (f : 𝒮 V) :
    zeroTermFin D f = D.zeroTerm (V.ω g (V.projReal (V.ω (1, g⁻¹.2) f))) := by
  simp [zeroTermFin, hg, omega_integrated, rep_apply_apply, mk_one_one]

/-- Let `D` be a splitting of `V` over `V₀`: dual isotropic frames `k`, `l` with columns indexed by
`p` and an isometry of `V₀` onto their orthogonal complement. The finite part
`zeroTermFin D : 𝒮 V → 𝒮 V₀` of the zero term along `k` does not vanish on `V.finitePart`, the span
of the finite Heisenberg translates of the vacuum. -/
lemma exists_zeroTermFin_ne_zero (D : V.Splitting V₀ p) :
    ∃ f ∈ V.finitePart, zeroTermFin D f ≠ 0 := by
  -- At `ω (1, g_f) vacElem` it is the zero term of `ω g vacElem`, a nonzero multiple of the vacuum.
  set g : G E s := (D.exists_isAdapted_and_frame_eq 1).choose with hg_def
  have hg : D.IsAdapted g 1 := (D.exists_isAdapted_and_frame_eq 1).choose_spec.1
  obtain ⟨c, hc_ne, hc⟩ : ∃ c ≠ (0 : ℂ), ∀ x : p → 𝔸 E,
      D.slice x (V.ω g V.vacElem) = (c * ‖vacuumFn x‖ ^ 2) • V₀.vacElem := by
    simpa using hg.slice_omega_vacElem
  refine ⟨V.ω (1, g.2) V.vacElem, omega_mem_finitePart _ vacElem_mem_finitePart, fun h_zero ↦ ?_⟩
  have h_value : zeroTermFin D (V.ω (1, g.2) V.vacElem) = c • V₀.vacElem := by
    rw [zeroTermFin_eq D hg_def, rep_apply_apply, ← slice_zero]
    simp [mk_one_one, hc, vacuumFn]
  have h_vac : V₀.vacElem = 0 := (smul_eq_zero.1 (h_value.symm.trans h_zero)).resolve_left hc_ne
  simpa [h_vac] using V₀.dataInner_vacElem_vacElem

unseal finitePart in
/-- Let `D` be a splitting of `V` over `V₀`, with isotropic frame `k` indexed by `p`. The finite
part `zeroTermFin D : 𝒮 V → 𝒮 V₀` of the zero term along `k` sends `V.finitePart`, the span of the
finite Heisenberg translates of the vacuum, into `V₀.finitePart`. -/
lemma zeroTermFin_mem_finitePart (D : V.Splitting V₀ p) {f : 𝒮 V} (hf : f ∈ V.finitePart) :
    zeroTermFin D f ∈ V₀.finitePart := by
  -- For the adapted point `g`, the mixed model of `ω g vacElem` is a multiple of `vacElem`. So the
  -- zero term of `ω g` of a finite translate of `vacElem` is a multiple of such a translate.
  set g : G E s := (D.exists_isAdapted_and_frame_eq 1).choose with hg_def
  have hg : D.IsAdapted g 1 := (D.exists_isAdapted_and_frame_eq 1).choose_spec.1
  obtain ⟨c, -, hc⟩ := hg.slice_omega_vacElem
  have h_translate (x : n → 𝔸f E) :
      D.zeroTerm (V.ω g (V.finHeisenbergOp x V.vacElem)) ∈ V₀.finitePart := by
    simp only [finHeisenbergOp, _root_.smul_apply, map_smul, omega_rho, mulVec_finVec, ← slice_zero,
      isMixedLaw_slice, hc]
    exact Submodule.smul_mem _ _ <| Submodule.smul_mem _ _ <| Submodule.smul_mem _ _ <|
      rho_finVec_mem_finitePart _ vacElem_mem_finitePart
  have h_le : V.finitePart ≤ V₀.finitePart.comap (D.zeroTerm ∘L V.ω g).toLinearMap := by
    simpa [finitePart, Submodule.span_le, Set.range_subset_iff] using h_translate
  rw [zeroTermFin_eq D hg_def, projReal_eq_self_of_mem_finitePart (omega_mem_finitePart _ hf)]
  exact h_le (omega_mem_finitePart _ hf)

/-- Let `D` be a splitting of `V` over `V₀`. The zero term along the isotropic frame of `D` carries
a translated pure tensor to a pure tensor: for an adelic vector `y` and a real Fock vector `v` of
`V` there is a real Fock vector `v₀` of `V₀`, independent of `f`, such that the zero term of
`ϱ(y) (v ⊗ f)` is `v₀ ⊗ zeroTermFin D (ϱ_f(α⁻¹ y_f) f)`, where `ϱ_f` is `V.finHeisenbergOp`, `⊗` is
`integrated` and `α⁻¹ y_f` is `finCoord y`. -/
lemma exists_zeroTerm_rho_integrated_eq (D : V.Splitting V₀ p) (y : n → 𝔸 E)
    (v : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E s))) :
    ∃ v₀ : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E s₀)), ∀ f : 𝒮 V,
      D.zeroTerm (V.ϱ y (V.integrated v f)) =
        V₀.integrated v₀ (zeroTermFin D (V.finHeisenbergOp (finCoord y) f)) := by
  -- Move `ϱ y` into the real datum `w` and the finite datum, and write `integrated w f` as `ω g`
  -- of another pure tensor. As `g` is adapted, there is a bounded map `L` of Fock spaces
  -- such that the zero term of `ω g (integrated v f)` is `integrated (L v)` of the zero term of
  -- `ω g (projReal f)`.
  set g : G E s := (D.exists_isAdapted_and_frame_eq 1).choose with hg_def
  have hg : D.IsAdapted g 1 := (D.exists_isAdapted_and_frame_eq 1).choose_spec.1
  obtain ⟨w, hw⟩ := V.exists_rho_integrated_eq y v
  obtain ⟨L, hL⟩ := hg.exists_apply_zero_omega_integrated_eq D.isMixedLaw_slice
  refine ⟨L (realWeil (blockU g⁻¹.1) w), fun f ↦ ?_⟩
  have h_integrated_eq_omega (f : 𝒮 V) :
      V.integrated w f = V.ω g (V.integrated (realWeil (blockU g⁻¹.1) w) (V.ω (1, g⁻¹.2) f)) := by
    rw [← V.omega_integrated]
    simp [rep_apply_apply]
  rw [hw, h_integrated_eq_omega, zeroTermFin_eq D hg_def, ← slice_zero, hL]

/-- Let `D` be a splitting of `V` over `V₀`, with isotropic frame `k`, dual frame `l` and embedding
`i` of `V₀`. In `D.finFrameVector g t a w b` the frame is moved by `g` and `t`; with both equal to
`1` and `a = 0` it is the vector `z = i w + k b`. Then `zeroTermFin D`, the finite part of the zero
term along `k`, carries translation of `V` by `z` to translation of `V₀` by `w`. -/
lemma zeroTermFin_finHeisenbergOp_finFrameVector (D : V.Splitting V₀ p) (b : p → 𝔸f E)
    {z : n → 𝔸f E} {w : n₀ → 𝔸f E} (hz : z = D.finFrameVector 1 1 0 w b) (f : 𝒮 V) :
    zeroTermFin D (V.finHeisenbergOp z f) = V₀.finHeisenbergOp w (zeroTermFin D f) := by
  have h_char : semichar z = semichar w := by simp [semichar, hz, star_dot_finFrameVector]
  have h_real (v : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E s))) :
      V.integrated v (V.ϱ (finVec z) f) = V.ϱ (finVec z) (V.integrated v f) :=
    (V.rho_integrated v f fun _ ↦ rfl).symm
  -- The law of the mixed model, where `z` has coordinates `w`, `b` and `0` in the frame.
  have h_law (f' : 𝒮 V) : D.zeroTerm (V.ϱ (finVec z) f') = V₀.ϱ (finVec w) (D.zeroTerm f') := by
    simp [hz, ← slice_zero, frameAt, finFrameVector, ← RingHom.coe_snd, fromCols_map,
      mulVec_finVec, mulVec_add, ← Matrix.map_mul]
  simp [finHeisenbergOp, zeroTermFin, h_char, h_real, h_law]

/-- Let `D` be a splitting of `V`, `k = D.kAdelic.map snd` the finite part of its isotropic frame
and `k^⊥` the kernel of `kᴴ`. Let `M * M'ᴴ = 1` and let `f` be fixed by the finite Heisenberg
operators of all `M x` with `x` in the standard lattice `Ô ^ n`. If `zeroTermFin D`, the finite part
of the zero term along `k`, does not vanish at the translate of `f` by `y`, then
`y ∈ M' Ô ^ n + k^⊥`. -/
lemma exists_sub_orthogonal_of_zeroTermFin_ne_zero (D : V.Splitting V₀ p) (M M' : Matrix n n (𝔸f E))
    {f : 𝒮 V} {y : n → 𝔸f E} (h_ne : zeroTermFin D (V.finHeisenbergOp y f) ≠ 0) (hM : M * M'ᴴ = 1)
    (hf : ∀ x ∈ stdLattice E n, V.finHeisenbergOp (M *ᵥ x) f = f) :
    ∃ l ∈ stdLattice E n, (D.kAdelic.map snd)ᴴ *ᵥ (y - M' *ᵥ l) = 0 := by
  -- Rescale the isotropic frame `k` by `t` so that `M'ᴴ * k * t` is integral with an integral left
  -- inverse `L`. Then `v = (k * t)ᴴ *ᵥ y` is integral, and `l = Lᴴ *ᵥ v` works.
  set k : Matrix n p (𝔸f E) := D.kAdelic.map snd with hk
  have h_left : D.kCoord.map snd * M * (M'ᴴ * k) = 1 := by
    simp [hk, ← M.mul_assoc, hM, ← RingHom.coe_snd, Matrix.mul_assoc, ← Matrix.map_mul]
  obtain ⟨t, -, h_int, L, hL, h_inv⟩ : ∃ t : GL p (𝔸f E), t.val.BlockTriangular (0 : p → ℕ) ∧
      IsIntMatrix (Ô E) (M'ᴴ * k * t.val) ∧
        ∃ L : Matrix p n (𝔸f E), IsIntMatrix (Ô E) L ∧ L * (M'ᴴ * k * t.val) = 1 :=
    isValuationPair_Ô.exists_isPrimitiveMatrix_mul ⟨D.kCoord.map snd * M, h_left⟩
  set v : p → 𝔸f E := star t.val *ᵥ kᴴ *ᵥ y with hv
  have hv_mem : v ∈ stdLattice E p := by
    -- The lattice is its own dual: it suffices that `selfDualAddChar E (star x ⬝ᵥ v) = 1` for
    -- integral `x`.
    refine mem_stdLattice_iff_selfDualAddChar.2 fun x hx ↦ ?_
    -- The isotropic vector `z` is a period of `f` and of `zeroTermFin D`, so its commutator with
    -- `y` fixes the nonzero vector `zeroTermFin D (V.finHeisenbergOp y f)`.
    set z : n → 𝔸f E := k *ᵥ t.val *ᵥ x with hz
    have h_period : V.finHeisenbergOp z f = f := by
      simpa [hz, ← M.mul_assoc, hM] using hf _ (h_int.mulVec hx)
    have hz_frame : z = D.finFrameVector 1 1 0 0 (t.val *ᵥ x) := by
      simp [hz, hk, frameAt, finFrameVector, fromCols_map]
    have h_zeroTermFin_invariant (f' : 𝒮 V) :
        zeroTermFin D (V.finHeisenbergOp z f') = zeroTermFin D f' := by
      rw [zeroTermFin_finHeisenbergOp_finFrameVector D _ hz_frame]
      simp [finHeisenbergOp, semichar]
    have h_comm : V.finHeisenbergOp y f = selfDualAddChar E (star z ⬝ᵥ y) • V.finHeisenbergOp z
      (V.finHeisenbergOp y f) := by
      rw [← V.finHeisenbergOp_comm, h_period]
    have h_dot : star x ⬝ᵥ v = star z ⬝ᵥ y := by
      simp [hv, hz, star_mulVec, ← dotProduct_mulVec, star_eq_conjTranspose]
    have h_fixed : selfDualAddChar E (star x ⬝ᵥ v) • zeroTermFin D (V.finHeisenbergOp y f) =
        (1 : ℂ) • zeroTermFin D (V.finHeisenbergOp y f) := by
      rw [h_dot, one_smul]
      conv_rhs => rw [h_comm, map_smul, h_zeroTermFin_invariant]
    exact smul_left_injective ℂ h_ne h_fixed
  have h_solve : star t.val *ᵥ kᴴ *ᵥ M' *ᵥ Lᴴ *ᵥ v = v := by
    have h_adjoint : star t.val * (kᴴ * (M' * Lᴴ)) = 1 := by
      simpa [Matrix.mul_assoc, star_eq_conjTranspose] using congrArg conjTranspose h_inv
    simp only [mulVec_mulVec, h_adjoint, one_mulVec]
  refine ⟨Lᴴ *ᵥ v, hL.conjTranspose.mulVec hv_mem,
    mulVec_injective_of_isUnit t.isUnit.star ?_⟩
  simp only [mulVec_sub, ← hv, h_solve, sub_self, mulVec_zero]

/-- The finite part of the embedding of `V₀` in `V`, in the coordinates of the lattices. -/
noncomputable abbrev _root_.New.Space.Splitting.iFin (D : V.Splitting V₀ p) :
    Matrix n n₀ (𝔸f E) :=
  D.iAdelic.map snd

/-- The finite part of the isotropic frame, in the coordinates of the lattice. Its columns span the
isotropic subspace `I`. -/
noncomputable abbrev _root_.New.Space.Splitting.isotropicBasisFin (D : V.Splitting V₀ p) :
    Matrix n p (𝔸f E) :=
  D.kAdelic.map snd

/-- The lattice `L'` of `V₀ = I^⊥ / I`: the image of `L ∩ I^⊥`, where `L` is the standard lattice
of `V` and `I` is spanned by the columns of `k = D.isotropicBasisFin`. A vector of `I^⊥` is written
`i w + k b` with `i = D.iFin`, and `w` is its class. -/
noncomputable def zeroTermLattice (D : V.Splitting V₀ p) : AddSubgroup (n₀ → 𝔸f E) where
  carrier := {w : n₀ → 𝔸f E |
    ∃ b : p → 𝔸f E, D.iFin *ᵥ w + D.isotropicBasisFin *ᵥ b ∈ stdLattice E n}
  add_mem' := fun ⟨b, hb⟩ ⟨b', hb'⟩ ↦
    ⟨b + b', by simpa [mulVec_add, add_add_add_comm] using add_mem hb hb'⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := fun ⟨b, hb⟩ ↦ ⟨-b, by simpa [mulVec_neg, add_comm] using neg_mem hb⟩

section

omit [WeilData E]

/-- With `g = 1`, `t = 1` and no component `a` along the dual frame `l`, `D.finFrameVector` is
`D.iFin *ᵥ w + D.isotropicBasisFin *ᵥ b`, the finite vector `i w + k b`. -/
lemma finFrameVector_zero (D : V.Splitting V₀ p) (w : n₀ → 𝔸f E) (b : p → 𝔸f E) :
    D.finFrameVector 1 1 0 w b = D.iFin *ᵥ w + D.isotropicBasisFin *ᵥ b := by
  simp [finFrameVector, frameAt, fromCols_map, iFin, isotropicBasisFin, add_comm]

/-- For the vector `D.finFrameVector 1 1 a w b = l a + i w + k b`, the coordinates `a` along the
dual frame `l` and `w` along `V₀` are its products with the columns of `k = D.isotropicBasisFin` and
of `i = D.iFin`. -/
lemma conjTranspose_isotropicBasisFin_iFin_mulVec_finFrameVector (D : V.Splitting V₀ p)
    (a b : p → 𝔸f E) (w : n₀ → 𝔸f E) :
    D.isotropicBasisFinᴴ *ᵥ D.finFrameVector 1 1 a w b = a ∧
      D.iFinᴴ *ᵥ D.finFrameVector 1 1 a w b = w := by
  have h_coord : ((D.frameAt 1 1).map snd)ᴴ *ᵥ D.finFrameVector 1 1 a w b = b ⊕ᵥ a ⊕ᵥ w :=
    D.adjoint_mulVec_finFrameVector 1 1 a w b
  generalize D.finFrameVector 1 1 a w b = z at h_coord ⊢
  obtain ⟨⟨-, h_dual⟩, h_class⟩ :
      ((D.lAdelic.map snd)ᴴ *ᵥ z = b ∧ D.isotropicBasisFinᴴ *ᵥ z = a) ∧ D.iFinᴴ *ᵥ z = w := by
    simpa [frameAt, fromCols_map, conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Sum.elim_eq_iff] using h_coord
  exact ⟨h_dual, h_class⟩

/-- A finite adelic vector orthogonal to the columns of the isotropic frame
`k = D.isotropicBasisFin` has the form `i w + k b`, where `i = D.iFin` is the embedding of `V₀`. -/
lemma exists_eq_iFin_add_isotropicBasisFin_of_mulVec_eq_zero (D : V.Splitting V₀ p)
    {z : n → 𝔸f E} (hz : D.isotropicBasisFinᴴ *ᵥ z = 0) :
    ∃ (w : n₀ → 𝔸f E) (b : p → 𝔸f E), z = D.iFin *ᵥ w + D.isotropicBasisFin *ᵥ b := by
  obtain ⟨a, w, b, rfl⟩ := D.exists_eq_finFrameVector 1 1 z
  have h_dual := (conjTranspose_isotropicBasisFin_iFin_mulVec_finFrameVector D a b w).1
  obtain rfl : a = 0 := h_dual.symm.trans hz
  exact ⟨w, b, finFrameVector_zero D w b⟩

end

/-- The finite zero term of the vacuum translated by `y` is `0` unless `y = i w + k b + l` with `l`
in the standard lattice, where `i = D.iFin` embeds `V₀` and `k = D.isotropicBasisFin` is the
isotropic frame. -/
lemma exists_eq_add_of_zeroTermFin_ne_zero (D : V.Splitting V₀ p) {y : n → 𝔸f E}
    (h_ne : zeroTermFin D (V.finHeisenbergOp y V.vacElem) ≠ 0) :
    ∃ l ∈ stdLattice E n, ∃ (w : n₀ → 𝔸f E) (b : p → 𝔸f E),
      y = D.iFin *ᵥ w + D.isotropicBasisFin *ᵥ b + l := by
  obtain ⟨l, hl, h_perp⟩ : ∃ l ∈ stdLattice E n, D.isotropicBasisFinᴴ *ᵥ (y - l) = 0 := by
    simpa using exists_sub_orthogonal_of_zeroTermFin_ne_zero D 1 1 h_ne (by simp)
      fun x hx ↦ by rw [one_mulVec, finHeisenbergOp_vacElem hx]
  obtain ⟨w, b, h_sub⟩ := exists_eq_iFin_add_isotropicBasisFin_of_mulVec_eq_zero D h_perp
  exact ⟨l, hl, w, b, sub_eq_iff_eq_add.1 h_sub⟩

/-- The translates of the vacuum under the finite Heisenberg operators of `x` and of `x + l`, with
`l` in the standard lattice `Ô ^ n`, agree up to a root of unity. -/
lemma exists_finHeisenbergOp_add_vacElem (W : Space E n s) (x : n → 𝔸f E) {l : n → 𝔸f E}
    (hl : l ∈ stdLattice E n) :
    ∃ ζ : ℂ, IsOfFinOrder ζ ∧
      W.finHeisenbergOp x W.vacElem = ζ • W.finHeisenbergOp (x + l) W.vacElem := by
  -- `selfDualAddChar E` is a multiplicative shift of `ψf E`, so its values have finite order.
  refine ⟨selfDualAddChar E (star traceOneAdele * star l ⬝ᵥ x), isOfFinOrder_ψf _, ?_⟩
  rw [← W.finHeisenbergOp_finHeisenbergOp, finHeisenbergOp_vacElem hl]

/-- For `y = i w + k b + l` with `l` in the standard lattice, `i = D.iFin` and
`k = D.isotropicBasisFin`, the finite zero term of the vacuum translated by `y` is a root of unity
times the translate by `w` of the finite zero term of the vacuum. -/
lemma exists_zeroTermFin_finHeisenbergOp_add (D : V.Splitting V₀ p) (w : n₀ → 𝔸f E)
    (b : p → 𝔸f E) {l : n → 𝔸f E} (hl : l ∈ stdLattice E n) :
    ∃ ζ : ℂ, IsOfFinOrder ζ ∧
      zeroTermFin D (V.finHeisenbergOp (D.iFin *ᵥ w + D.isotropicBasisFin *ᵥ b + l) V.vacElem) =
        ζ • V₀.finHeisenbergOp w (zeroTermFin D V.vacElem) := by
  obtain ⟨ζ, hζ, h_shift⟩ : ∃ ζ : ℂ, IsOfFinOrder ζ ∧
      V.finHeisenbergOp (D.iFin *ᵥ w + D.isotropicBasisFin *ᵥ b + l) V.vacElem =
        ζ • V.finHeisenbergOp (D.iFin *ᵥ w + D.isotropicBasisFin *ᵥ b + l + -l) V.vacElem :=
    exists_finHeisenbergOp_add_vacElem V _ (neg_mem hl)
  refine ⟨ζ, hζ, ?_⟩
  rw [h_shift, add_neg_cancel_right, map_smul,
    zeroTermFin_finHeisenbergOp_finFrameVector D b (finFrameVector_zero D w b).symm]

/-- The finite part `zeroTermFin D` of the zero term along a splitting `D` does not vanish at the
vacuum `V.vacElem`. -/
lemma zeroTermFin_vacElem_ne_zero (D : V.Splitting V₀ p) : zeroTermFin D V.vacElem ≠ 0 := by
  -- Otherwise it would vanish on all finite translates of the vacuum, which span the finite part.
  intro h_zero
  have h_translate (y : n → 𝔸f E) : zeroTermFin D (V.finHeisenbergOp y V.vacElem) = 0 := by
    by_contra h_ne
    obtain ⟨l, hl, w, b, rfl⟩ := exists_eq_add_of_zeroTermFin_ne_zero D h_ne
    obtain ⟨ζ, -, hζ⟩ := exists_zeroTermFin_finHeisenbergOp_add D w b hl
    simp [-zeroTermFin, hζ, h_zero] at h_ne
  have h_le : V.finitePart ≤ LinearMap.ker (zeroTermFin D).toLinearMap := by
    simpa [finitePart, Submodule.span_le, Set.range_subset_iff] using h_translate
  obtain ⟨f, hf, hf_ne⟩ := exists_zeroTermFin_ne_zero D
  exact hf_ne (h_le hf)

/-- For a splitting `D` of `V` over `V₀`, the translations by vectors of the lattice
`zeroTermLattice D` of `V₀` fix the value of the finite zero term `zeroTermFin D` at the vacuum. -/
lemma finHeisenbergOp_zeroTermFin_vacElem (D : V.Splitting V₀ p) {x : n₀ → 𝔸f E}
    (hx : x ∈ zeroTermLattice D) :
    V₀.finHeisenbergOp x (zeroTermFin D V.vacElem) = zeroTermFin D V.vacElem := by
  obtain ⟨b, hb⟩ := hx
  rw [← zeroTermFin_finHeisenbergOp_finFrameVector D b (finFrameVector_zero D x b).symm,
    finHeisenbergOp_vacElem hb]

/-- Let `W` be a hermitian space over `E` with a point, `s` the signs of its form at the infinite
places, and let `g` be in `Gf E n`, the finite adelic unitary group. Thus `(1, g)` is the adelic
point with trivial infinite part and `W.ω (1, g)` is its Weil operator. Let `Λ = Ô ^ n` be the
standard lattice and let the `r a` be representatives of `g Λ` modulo `g Λ ∩ Λ`. Then this operator
sends the vacuum to a nonzero multiple of the sum of the finite Heisenberg translates of the vacuum
by the `r a`. -/
lemma exists_omega_vacElem_eq_sum (W : Space E n s) {g : Gf E n} {R : Type*} [Fintype R]
    {r : R → n → 𝔸f E}
    (hr_mem : ∀ a : R, r a ∈ (stdLattice E n).map (DistribSMul.toAddMonoidHom (n → 𝔸f E) g))
    (hr_rep : ∀ z ∈ (stdLattice E n).map (DistribSMul.toAddMonoidHom (n → 𝔸f E) g),
      ∃! a : R, z - r a ∈ stdLattice E n) :
    ∃ c ≠ (0 : ℂ), W.ω (1, g) W.vacElem = c • ∑ a : R, W.finHeisenbergOp (r a) W.vacElem := by
  -- Write `r a = g (x a)`. The `x a` represent `Λ` modulo `H = Λ ∩ g⁻¹ Λ`.
  let H : AddSubgroup (stdLattice E n) :=
    ((stdLattice E n).comap g.val.val.mulVecLin).addSubgroupOf (stdLattice E n)
  have h_preimage : ∀ a : R, ∃ x : stdLattice E n, g.val.val *ᵥ x.val = r a := fun a ↦
    let ⟨x, hx, h_eq⟩ := hr_mem a
    ⟨⟨x, hx⟩, h_eq⟩
  choose x hx using h_preimage
  have h_class (a : R) (z : stdLattice E n) :
      (x a : stdLattice E n ⧸ H) = z ↔ g.val.val *ᵥ z.val - r a ∈ stdLattice E n := by
    rw [QuotientAddGroup.eq, ← hx, ← mulVec_sub, sub_eq_neg_add]
    rfl
  have h_bij : Function.Bijective fun a : R ↦ (x a : stdLattice E n ⧸ H) := by
    refine (Function.bijective_iff_existsUnique _).2 fun q ↦ ?_
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    simp only [h_class]
    exact hr_rep _ ⟨z, z.property, rfl⟩
  refine ⟨finMultiplier g / ‖finMultiplier g‖ ^ 2, by simp [finMultiplier_ne_zero], ?_⟩
  rw [omega_vacElem_sum, ← finsum_comp _ h_bij, finsum_eq_sum_of_fintype]
  simp only [W.finHeisenbergOp_mulVec_out_vacElem (x := x _) rfl, hx]

section

omit [WeilData E]

/-- Let `i = D.iFin` be the embedding of `V₀` and `k = D.isotropicBasisFin` the isotropic frame. For
`B = i g + k c` with `g` unitary, the adjoint of `B` sends `i w + k b` to `g⁻¹ w`. -/
lemma conjTranspose_mulVec_iFin_add_isotropicBasisFin {D : V.Splitting V₀ p} {g : Gf E n₀}
  {c : Matrix p n₀ (𝔸f E)}
    {B : Matrix n n₀ (𝔸f E)} (hB_def : B = D.iFin * (g : Matrix n₀ n₀ (𝔸f E)) + D.isotropicBasisFin
      * c)
    (w : n₀ → 𝔸f E) (b : p → 𝔸f E) :
    Bᴴ *ᵥ (D.iFin *ᵥ w + D.isotropicBasisFin *ᵥ b) = (↑g⁻¹ : Matrix n₀ n₀ (𝔸f E)) *ᵥ w := by
  obtain ⟨h_perp, h_class⟩ : D.isotropicBasisFinᴴ *ᵥ D.finFrameVector 1 1 0 w b = 0 ∧
      D.iFinᴴ *ᵥ D.finFrameVector 1 1 0 w b = w :=
        conjTranspose_isotropicBasisFin_iFin_mulVec_finFrameVector D 0 b w
  rw [← finFrameVector_zero, hB_def, U.inv_val_eq_conjTranspose]
  simp [add_mulVec, ← mulVec_mulVec, h_perp, h_class]

/-- Let `D` be a splitting of `V` over `V₀`, with finite parts `i = D.iFin` of the embedding of `V₀`
and `k = D.isotropicBasisFin` of the isotropic frame. If `g` is unitary and `B = i g + k c` has
entries in `Ô`, then `zeroTermLattice D` contains `g Ô ^ n₀`. -/
lemma map_stdLattice_le_zeroTermLattice {D : V.Splitting V₀ p} {g : Gf E n₀}
    {c : Matrix p n₀ (𝔸f E)} {B : Matrix n n₀ (𝔸f E)}
    (hB_def : B = D.iFin * (g : Matrix n₀ n₀ (𝔸f E)) + D.isotropicBasisFin * c)
      (hB : IsIntMatrix (Ô E) B) :
    (stdLattice E n₀).map (DistribSMul.toAddMonoidHom (n₀ → 𝔸f E) g) ≤ zeroTermLattice D := by
  -- For `x` integral, `B x` is a lattice vector of class `g x`.
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨c *ᵥ x, ?_⟩
  change D.iFin *ᵥ (g : Matrix n₀ n₀ (𝔸f E)) *ᵥ x + D.isotropicBasisFin *ᵥ c *ᵥ x ∈ stdLattice E n
  simpa only [hB_def, add_mulVec, ← mulVec_mulVec] using! hB.mulVec hx

/-- Let `D` be a splitting of `V` over `V₀`, with finite parts `i = D.iFin` of the embedding of `V₀`
and `k = D.isotropicBasisFin` of the isotropic frame. The lattice `zeroTermLattice D` consists of
the `w` with `i w + k b ∈ Ô ^ n` for some `b`. If `g` is unitary and `B = i g + k c` has entries in
`Ô`, then this lattice is `g Ô ^ n₀`: a vector `w` lies in it if and only if `g⁻¹ w ∈ Ô ^ n₀`. -/
lemma mem_zeroTermLattice_iff {D : V.Splitting V₀ p} {g : Gf E n₀} {c : Matrix p n₀ (𝔸f E)}
    {B : Matrix n n₀ (𝔸f E)} (hB_def : B = D.iFin * (g : Matrix n₀ n₀ (𝔸f E)) + D.isotropicBasisFin
      * c)
    (hB : IsIntMatrix (Ô E) B) {w : n₀ → 𝔸f E} :
    w ∈ zeroTermLattice D ↔ (↑g⁻¹ : Matrix n₀ n₀ (𝔸f E)) *ᵥ w ∈ stdLattice E n₀ := by
  constructor
  · -- The integral matrix `Bᴴ` sends a lattice vector of class `w` to `g⁻¹ w`.
    rintro ⟨b, hb⟩
    simpa only [conjTranspose_mulVec_iFin_add_isotropicBasisFin hB_def w b] using!
      hB.conjTranspose.mulVec hb
  · exact fun hx ↦ map_stdLattice_le_zeroTermLattice hB_def hB ⟨_, hx, smul_inv_smul g w⟩

end

/-- Let `D` be a splitting of `V` over `V₀`, with finite parts `i = D.iFin` of the embedding of `V₀`
and `k = D.isotropicBasisFin` of the isotropic frame, whose columns are indexed by `p`. There are a
finite point `g` of the unitary group of `V₀` and a matrix `c` such that `i g + k c` has entries in
`Ô`. -/
lemma exists_isIntMatrix_iFin_mul_add_isotropicBasisFin_mul (D : V.Splitting V₀ p) :
    ∃ (g : Gf E n₀) (c : Matrix p n₀ (𝔸f E)),
      IsIntMatrix (Ô E) (D.iFin * (g : Matrix n₀ n₀ (𝔸f E)) + D.isotropicBasisFin * c) := by
  -- Take `h` adapted to the splitting with `h⁻¹` a radical element times a Levi element. The lift
  -- is the finite part of `h⁻¹ i`, a block of the adapted frame.
  obtain ⟨c, b, a, g, h, h_adapted, h_one⟩ : ∃ (c : Matrix n₀ p (𝔸 E)) (b : Matrix p p (𝔸 E))
      (a : GL p (𝔸 E)) (g : G E s₀) (h : G E s),
      D.IsAdapted h 1 ∧ 1 = D.radicalElement c b * D.levi (a, g) * h :=
    D.exists_eq_radicalElement_mul_levi_mul_isAdapted 1
  have h_inv : D.radicalElement c b * D.levi (a, g) = h⁻¹ := eq_inv_of_mul_eq_one_left h_one.symm
  set c' : Matrix p n₀ (𝔸 E) := cᴴ * stdForm E s₀ * g.adeleMatrix with hc'
  have h_col : h⁻¹.adeleMatrix * D.iAdelic = D.iAdelic * g.adeleMatrix + D.kAdelic * c' := by
    rw [← h_inv, G.adeleMatrix_mul, Matrix.mul_assoc, levi_mul_iAdelic,
      ← Matrix.mul_assoc, radicalElement_mul_iAdelic, Matrix.add_mul, hc',
        Matrix.mul_assoc D.kAdelic]
  refine ⟨g.2, c'.map snd, fun i j ↦ ?_⟩
  have h_entry : (D.iFin * (g.2 : Matrix n₀ n₀ (𝔸f E)) + D.isotropicBasisFin * c'.map snd) i j =
      ((h⁻¹.adeleMatrix * D.iAdelic) i j).2 := by
    rw [h_col]
    simp [Matrix.mul_apply, Prod.snd_sum]
  simpa [h_entry, frameAt, Matrix.mul_fromCols] using h_adapted.2 i (Sum.inr j)

/-- The lattice `L' = zeroTermLattice D` is the image of the standard lattice of `V₀` under a finite
point of the unitary group. -/
lemma exists_zeroTermLattice_eq_map (D : V.Splitting V₀ p) :
    ∃ g : Gf E n₀,
      zeroTermLattice D = (stdLattice E n₀).map (DistribSMul.toAddMonoidHom (n₀ → 𝔸f E) g) := by
  obtain ⟨g, c, hB⟩ := exists_isIntMatrix_iFin_mul_add_isotropicBasisFin_mul D
  exact ⟨g, le_antisymm (fun w hw ↦ ⟨g⁻¹ • w, (mem_zeroTermLattice_iff rfl hB).1 hw,
    smul_inv_smul g w⟩) (map_stdLattice_le_zeroTermLattice rfl hB)⟩

/-- For a finite point `g` of the unitary group, the image `g Ô ^ n` of the standard lattice is its
own dual: it consists of the `w` with `selfDualAddChar E (x* w) = 1` for all `x` in it. Here
`selfDualAddChar E` is the character of the finite adeles for which `Ô` is self-dual. -/
lemma mem_map_stdLattice_iff_selfDualAddChar (g : Gf E n) {w : n → 𝔸f E} :
    w ∈ (stdLattice E n).map (DistribSMul.toAddMonoidHom (n → 𝔸f E) g) ↔
      ∀ x ∈ (stdLattice E n).map (DistribSMul.toAddMonoidHom (n → 𝔸f E) g),
        selfDualAddChar E (star x ⬝ᵥ w) = 1 := by
  -- The standard lattice is its own dual, and `g` keeps the pairing.
  obtain ⟨v, rfl⟩ : ∃ v : n → 𝔸f E, g • v = w := MulAction.surjective g w
  have h_dot (y : n → 𝔸f E) : star (g • y) ⬝ᵥ g • v = star y ⬝ᵥ v := by
    change star ((g : Matrix n n (𝔸f E)) *ᵥ y) ⬝ᵥ (g : Matrix n n (𝔸f E)) *ᵥ v = star y ⬝ᵥ v
    simp [star_mulVec, ← dotProduct_mulVec, ← U.inv_val_eq_conjTranspose]
  have h_mem : g • v ∈ (stdLattice E n).map (DistribSMul.toAddMonoidHom (n → 𝔸f E) g) ↔
      v ∈ stdLattice E n :=
    AddSubgroup.mem_map_iff_mem (MulAction.injective g)
  rw [h_mem, mem_stdLattice_iff_selfDualAddChar]
  simp [h_dot]

/-- The lattice `L' = zeroTermLattice D` is unimodular: it consists of the `w` with
`selfDualAddChar E (x* w) = 1` for all `x` in `L'`. -/
lemma mem_zeroTermLattice_iff_selfDualAddChar (D : V.Splitting V₀ p) {w : n₀ → 𝔸f E} :
    w ∈ zeroTermLattice D ↔ ∀ x ∈ zeroTermLattice D, selfDualAddChar E (star x ⬝ᵥ w) = 1 := by
  obtain ⟨g, hg⟩ := exists_zeroTermLattice_eq_map D
  simpa only [hg] using mem_map_stdLattice_iff_selfDualAddChar g

/-- If `L' = zeroTermLattice D` contains the image of the standard lattice under a unitary element,
the two lattices are equal, because each is its own dual. -/
lemma zeroTermLattice_eq_map_of_le (D : V.Splitting V₀ p) {g : Gf E n₀}
    (h_le : (stdLattice E n₀).map (DistribSMul.toAddMonoidHom (n₀ → 𝔸f E) g) ≤
      zeroTermLattice D) :
    zeroTermLattice D = (stdLattice E n₀).map (DistribSMul.toAddMonoidHom (n₀ → 𝔸f E) g) :=
  le_antisymm (fun _ hw ↦ (mem_map_stdLattice_iff_selfDualAddChar g).2 fun x hx ↦
    (mem_zeroTermLattice_iff_selfDualAddChar D).1 hw x (h_le hx)) h_le

/-- For `g` unitary and `Λ` the standard lattice, `g Λ ∩ Λ` has finite index in `g Λ`. -/
lemma relIndex_map_stdLattice_ne_zero (g : Gf E n) :
    (stdLattice E n).relIndex
      ((stdLattice E n).map (DistribSMul.toAddMonoidHom (n → 𝔸f E) g)) ≠ 0 := by
  -- The index is the squared norm of the nonzero number `finMultiplier g`.
  intro h_zero
  have h_norm : ‖finMultiplier g‖ ^ 2 = (stdLattice E n).relIndex
      ((stdLattice E n).map (DistribSMul.toAddMonoidHom (n → 𝔸f E) g)) := by
    rw [norm_finMultiplier_sq, AddSubgroup.relIndex_comap]
    rfl
  simp [h_zero, finMultiplier_ne_zero] at h_norm

/-- Let `D` be a splitting of `V` over `V₀`, with embedding `i = D.iFin` and isotropic frame
`k = D.isotropicBasisFin`. Let `L' = zeroTermLattice D` be the lattice of the `w` with
`i w + k b ∈ Ô ^ n` for some `b`, and let the `r a` be representatives of `L'` modulo `L' ∩ Ô ^ n₀`.
Then `zeroTermFin D` sends the vacuum of `V` to a nonzero multiple of the sum of the finite
Heisenberg translates of the vacuum of `V₀` by the `r a`. -/
lemma exists_zeroTermFin_vacElem_eq_sum (D : V.Splitting V₀ p) {R : Type*} [Fintype R]
    {r : R → n₀ → 𝔸f E} (hr_mem : ∀ a : R, r a ∈ zeroTermLattice D)
    (hr_rep : ∀ z ∈ zeroTermLattice D, ∃! a : R, z - r a ∈ stdLattice E n₀) :
    ∃ c ≠ (0 : ℂ), zeroTermFin D V.vacElem = c • ∑ a : R, V₀.finHeisenbergOp (r a) V₀.vacElem := by
  obtain ⟨g, hg⟩ := exists_zeroTermLattice_eq_map D
  -- A vector fixed by the translations by `L' = g L°` is a multiple of `ω g` of the vacuum.
  obtain ⟨C, hC⟩ : ∃ C : ℂ, zeroTermFin D V.vacElem = C • V₀.ω (1, g) V₀.vacElem :=
    exists_eq_smul_omega_vacElem (zeroTermFin_mem_finitePart D vacElem_mem_finitePart) fun x hx ↦
      finHeisenbergOp_zeroTermFin_vacElem D (hg.ge ⟨x, hx, rfl⟩)
  have hC_ne : C ≠ 0 := fun hC_zero ↦ zeroTermFin_vacElem_ne_zero D (by rw [hC, hC_zero, zero_smul])
  rw [hg] at hr_mem hr_rep
  obtain ⟨c, hc_ne, hc⟩ := exists_omega_vacElem_eq_sum V₀ hr_mem hr_rep
  exact ⟨C * c, mul_ne_zero hC_ne hc_ne, by rw [hC, hc, mul_smul]⟩

/-- Let `D : V.Splitting V₀ p` be a splitting: `i = D.iFin` embeds `V₀` in `V` and the columns of
`k = D.isotropicBasisFin`, indexed by `p`, are an isotropic frame orthogonal to it. Let
`B = i g + k c` be integral with `g` unitary. Then `zeroTermFin D` sends the vacuum translated by
`y` to `0` or to a root of unity times the translate by `y₀ = g Bᴴ y` of its value at the vacuum. -/
lemma exists_zeroTermFin_finHeisenbergOp_eq_smul {D : V.Splitting V₀ p} {g : Gf E n₀}
    {c : Matrix p n₀ (𝔸f E)} {B : Matrix n n₀ (𝔸f E)}
    (hB_def : B = D.iFin * (g : Matrix n₀ n₀ (𝔸f E)) + D.isotropicBasisFin * c)
    (hB : IsIntMatrix (Ô E) B) (y : n → 𝔸f E) :
    ∃ ζ : ℂ, (ζ = 0 ∨ IsOfFinOrder ζ) ∧
      zeroTermFin D (V.finHeisenbergOp y V.vacElem) =
        ζ • V₀.finHeisenbergOp ((g : Matrix n₀ n₀ (𝔸f E)) *ᵥ Bᴴ *ᵥ y)
          (zeroTermFin D V.vacElem) := by
  by_cases h_zero : zeroTermFin D (V.finHeisenbergOp y V.vacElem) = 0
  · exact ⟨0, Or.inl rfl, by rw [h_zero, zero_smul]⟩
  obtain ⟨l, hl, w, b, rfl⟩ := exists_eq_add_of_zeroTermFin_ne_zero D h_zero
  obtain ⟨ζ, hζ, h_class⟩ : ∃ ζ : ℂ, IsOfFinOrder ζ ∧
      zeroTermFin D (V.finHeisenbergOp (D.iFin *ᵥ w + D.isotropicBasisFin *ᵥ b + l) V.vacElem) =
        ζ • V₀.finHeisenbergOp w (zeroTermFin D V.vacElem) :=
    exists_zeroTermFin_finHeisenbergOp_add D w b hl
  -- The class `w` differs from `g Bᴴ y` by `x = g Bᴴ l`, an element of `zeroTermLattice D`.
  let x : n₀ → 𝔸f E := g.val.val *ᵥ Bᴴ *ᵥ l
  have hx : x ∈ zeroTermLattice D := by
    have h_int : Bᴴ *ᵥ l ∈ stdLattice E n₀ := hB.conjTranspose.mulVec hl
    simpa [x, mem_zeroTermLattice_iff hB_def hB] using h_int
  have h_sum : g.val.val *ᵥ Bᴴ *ᵥ (D.iFin *ᵥ w + D.isotropicBasisFin *ᵥ b + l) = w + x := by
    rw [mulVec_add, conjTranspose_mulVec_iFin_add_isotropicBasisFin hB_def, mulVec_add]
    simp [x]
  refine ⟨ζ * selfDualAddChar E (star traceOneAdele * star x ⬝ᵥ w),
    Or.inr (hζ.mul (isOfFinOrder_ψf _)), ?_⟩
  rw [h_class, h_sum, mul_smul, ← V₀.finHeisenbergOp_finHeisenbergOp,
    finHeisenbergOp_zeroTermFin_vacElem D hx]

end FiniteZeroTerm

/-!
## Grade zero parts and equivariant splittings of the seesaw

Three hermitian spaces `V, V', V''` are each presented (`New.Grading`) as a definite part `X`, `X'`,
`X₀` plus a string of basis vectors. They are graded by `New.Grading.gradeOf`, which is zero on the
definite part. The three unitary groups act on data on `Hom (V', V⁻ ⊕ V'')` by
`New.Seesaw.tripleWeil`. For a splitting `D` of a space (`New.Space.Splitting`), `D.zeroTerm` is the
constant term along its isotropic frame, and `New.Seesaw.zeroTermFin D` is its finite part.
-/

section EdgePair

open Matrix Kronecker Space Fintype Function Exchange Grading Splitting

variable {E ι ι' ι'' X X' X'' X₀ q : Type} [Field E] [CMType E] [WeilData E] [Fintype ι]
  [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype ι''] [DecidableEq ι''] [Fintype X]
  [DecidableEq X] [Fintype X'] [DecidableEq X'] [Fintype X''] [DecidableEq X''] [Fintype X₀]
  [DecidableEq X₀] [Fintype q] [DecidableEq q] {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {ε'' : ι'' → ℤˣ}
  {s s' s'' : ℕ} {V : Space E ι ε} {V' : Space E ι' ε'} {V'' : Space E ι'' ε''} {N p : E}
  (Y : Grading V N X s) (Y' : Grading V' N X' s') (Y'' : Grading V'' N X₀ s'')

variable (V V'') in
/-- For integer weights (grades) on the basis of `V`, with `V.J` pairing only opposite weights: a
rational isometry from `V''` onto the span of the basis vectors of weight zero. -/
structure GradeZeroPart (wt : ι → ℤ) where
  /-- An injection that labels the indices of grade zero by the basis indices of `V''`. -/
  index : ι'' ↪ ι
  /-- The image of the injection is the set of indices of grade zero. -/
  mem_range_index (incl : ι) : incl ∈ Set.range index ↔ wt incl = 0
  /-- The matrix of the inclusion of `V''` in `V`. -/
  incl : Matrix ι ι'' E
  /-- The inclusion has no component along basis vectors of nonzero grade. -/
  incl_eq_zero (a : ι) (b : ι'') : wt a ≠ 0 → incl a b = 0
  /-- The inclusion pulls the Gram matrix of `V` back to that of `V''`. -/
  gram_incl : inclᴴ * V.J * incl = V''.J
  /-- The Gram matrix of `V` pairs two basis vectors only if their grades add up to zero. -/
  grade_add_eq_zero (a b : ι) : V.J a b ≠ 0 → wt a + wt b = 0

omit [WeilData E] in
/-- In rational coordinates, a pair of unitary points acts on `V ⊕ V'` by a block diagonal
matrix. -/
lemma ratCoordMatrix_sum (g : G E ε × G E ε') :
    (V.sum V').ratCoordMatrix (.sum g) =
      fromBlocks (V.ratCoordMatrix g.1) 0 0 (V'.ratCoordMatrix g.2) := by
  simp [ratCoordMatrix_eq, sum, blockGL, fromBlocks_multiply]

variable {w : ι → ℤ} (X'' q)

section

omit [WeilData E]

/-- The Gram matrix pairs weight `a` only with weight `-a`, so it intertwines the projections to the
positive and to the negative weights. -/
lemma GradeZeroPart.proj_pos_mul_J (Z : GradeZeroPart V V'' w) :
    (diagonal fun i : ι ↦ if 0 < w i then 1 else 0) * V.J =
      V.J * diagonal fun i : ι ↦ if w i < 0 then 1 else 0 := by
  ext a b
  by_cases hab : w a + w b = 0
  · simp [show 0 < w a ↔ w b < 0 by omega]
  · simp [by_contra fun h_ne ↦ hab (Z.grade_add_eq_zero _ _ h_ne)]

/-- The inverse of the Gram matrix of `V` vanishes at two indices of positive weight. -/
lemma GradeZeroPart.inv_J_apply_eq_zero_of_pos (Z : GradeZeroPart V V'' w) {a b : ι} (ha : 0 < w a)
    (hb : 0 < w b) : V.J⁻¹ a b = 0 := by
  set P : Matrix ι ι E := diagonal fun i : ι ↦ if 0 < w i then 1 else 0 with hP
  set Q : Matrix ι ι E := diagonal fun i : ι ↦ if w i < 0 then 1 else 0 with hQ
  have h_conj : V.J⁻¹ * P = Q * V.J⁻¹ := calc
    V.J⁻¹ * P = V.J⁻¹ * (P * V.J * V.J⁻¹) := by simp [Matrix.mul_assoc]
    _ = Q * V.J⁻¹ := by simp [show P * V.J = V.J * Q from Z.proj_pos_mul_J, Matrix.mul_assoc]
  simpa [hP, hQ, hb, ha.not_gt] using congr_fun₂ h_conj a b

/-- There are as many basis indices of positive weight as of negative weight. -/
lemma GradeZeroPart.card_pos_eq_card_neg (Z : GradeZeroPart V V'' w) :
    Fintype.card {i : ι // 0 < w i} = Fintype.card {i : ι // w i < 0} := by
  -- The two projections are conjugate by `V.J`, so they have the same trace.
  set P : Matrix ι ι E := diagonal fun i : ι ↦ if 0 < w i then 1 else 0 with hP
  set Q : Matrix ι ι E := diagonal fun i : ι ↦ if w i < 0 then 1 else 0 with hQ
  have h_trace : trace P = trace Q := calc
    trace P = trace (P * V.J * V.J⁻¹) := by simp [Matrix.mul_assoc]
    _ = trace Q := by simp [show P * V.J = V.J * Q from Z.proj_pos_mul_J, trace_mul_comm _ V.J⁻¹]
  simpa [hP, hQ, card_subtype] using h_trace

private lemma GradeZeroPart.splitting_gram_kk (Z : GradeZeroPart V V'' w) :
    (inclMatrix E (Subtype.val : {i : ι // 0 < w i} → ι))ᴴ * V.J *
      inclMatrix E (Subtype.val : {i : ι // 0 < w i} → ι) = 0 := by
  simp [inclMatrix, ← Matrix.ext_iff, Matrix.mul_apply, Matrix.one_apply]
  grind [→ Z.grade_add_eq_zero]

private lemma GradeZeroPart.splitting_gram_ll (Z : GradeZeroPart V V'' w) :
    (V.J⁻¹ * inclMatrix E (Subtype.val : {i : ι // 0 < w i} → ι))ᴴ * V.J *
      (V.J⁻¹ * inclMatrix E (Subtype.val : {i : ι // 0 < w i} → ι)) = 0 := by
  simpa [Matrix.mul_assoc, V.isHermitian_J.inv.eq, ← ext_iff, inclMatrix, Matrix.mul_apply,
    Matrix.one_apply] using fun a ha b hb ↦ Z.inv_J_apply_eq_zero_of_pos ha hb

private lemma GradeZeroPart.splitting_gram_lk (_Z : GradeZeroPart V V'' w) :
    (V.J⁻¹ * inclMatrix E (Subtype.val : {i : ι // 0 < w i} → ι))ᴴ * V.J *
      inclMatrix E (Subtype.val : {i : ι // 0 < w i} → ι) = 1 := by
  simp [Matrix.mul_assoc, V.isHermitian_J.inv.eq, inclMatrix, ← Matrix.ext_iff, Matrix.mul_apply,
    Matrix.one_apply]

private lemma GradeZeroPart.splitting_gram_ik (Z : GradeZeroPart V V'' w) :
    Z.inclᴴ * V.J * inclMatrix E (Subtype.val : {i : ι // 0 < w i} → ι) = 0 := by
  simp [inclMatrix, ← Matrix.ext_iff, Matrix.mul_apply, Matrix.one_apply]
  grind +splitImp [→ Z.grade_add_eq_zero, Z.incl_eq_zero, star_zero, Finset.sum_eq_zero]

private lemma GradeZeroPart.splitting_gram_il (Z : GradeZeroPart V V'' w) :
    Z.inclᴴ * V.J * (V.J⁻¹ * inclMatrix E (Subtype.val : {i : ι // 0 < w i} → ι)) = 0 := by
  simp [Matrix.mul_assoc, inclMatrix, ← Matrix.ext_iff, Matrix.mul_apply, Matrix.one_apply]
  grind [Z.incl_eq_zero]

private lemma GradeZeroPart.splitting_card_eq (Z : GradeZeroPart V V'' w) :
    Fintype.card ι = Fintype.card ι'' + 2 * Fintype.card {i : ι // 0 < w i} := by
  -- Count the indices by the sign of their weight.
  have h_total : Fintype.card ι = Fintype.card {i : ι // w i = 0} +
      (Fintype.card {i : ι // w i < 0} + Fintype.card {i : ι // 0 < w i}) := by
    simp [SignType.univ_eq, sign_eq_one_iff, sign_eq_neg_one_iff, card_subtype,
      ← card_congr (.sigmaFiberEquiv (SignType.sign ∘ w))]
  have h_zero : Fintype.card {i : ι // w i = 0} = Fintype.card ι'' := by
    simp [card_subtype, ← Z.mem_range_index, ← card_range Z.index]
  have h_pos_neg : Fintype.card {i : ι // 0 < w i} = Fintype.card {i : ι // w i < 0} :=
    Z.card_pos_eq_card_neg
  omega

omit [Fintype X'] in
private lemma GradeZeroPart.hom_mem_range_index (Z : GradeZeroPart V V'' w) (hs' : Even s')
    (hw : ∀ i : ι, Even (w i)) (r : ι × ι') :
    r ∈ Set.range (Z.index.prodMap (.trans .inl Y'.indexEquiv.toEmbedding)) ↔
      w r.1 - Y'.gradeOf r.2 = 0 := by
  revert r
  -- On the string of `V'` the weights are odd, as `s'` is even, so they differ from those of `V`.
  simp [reindex_equiv Y'.indexEquiv]
  grind [GradeZeroPart]

omit [Fintype X'] in
private lemma GradeZeroPart.hom_incl_eq_zero (Z : GradeZeroPart V V'' w)
    (a : ι × ι') (b : ι'' × X') :
    w a.1 - Y'.gradeOf a.2 ≠ 0 →
      (Z.incl ⊗ₖ inclMatrix E (Y'.indexEquiv ∘ Sum.inl)) a b = 0 := by
  revert a b
  simp [reindex_equiv Y'.indexEquiv, inclMatrix, Matrix.one_apply]
  grind [Z.incl_eq_zero]

private lemma GradeZeroPart.hom_gram_incl (Z : GradeZeroPart V V'' w) :
    (Z.incl ⊗ₖ inclMatrix E (Y'.indexEquiv ∘ Sum.inl))ᴴ * (V'.hom V).J *
        (Z.incl ⊗ₖ inclMatrix E (Y'.indexEquiv ∘ Sum.inl)) =
      ((stdSpace E X').hom V'').J := by
  rw [hom_J, hom_J, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul,
    Z.gram_incl]
  congr 1
  refine Matrix.ext fun a b ↦ ?_
  have h_imm : ((inclMatrix E (Y'.indexEquiv ∘ Sum.inl))ᴴ * V'.J⁻¹ᵀ *
      inclMatrix E (Y'.indexEquiv ∘ Sum.inl)) a b =
      V'.J⁻¹ᵀ (Y'.indexEquiv (Sum.inl a)) (Y'.indexEquiv (Sum.inl b)) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, inclMatrix, Matrix.submatrix_apply,
      id_eq, Function.comp_apply, Matrix.one_apply, apply_ite star, star_one, star_zero, ite_mul,
      one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte]
  rw [h_imm, Matrix.transpose_apply, Y'.J_inv_eq_gradedGram]
  simp [gradedGram, gradedBlocks, Matrix.one_apply, eq_comm]

private lemma GradeZeroPart.hom_grade_add_eq_zero (Z : GradeZeroPart V V'' w)
    (a b : ι × ι') :
    (V'.hom V).J a b ≠ 0 → (w a.1 - Y'.gradeOf a.2) + (w b.1 - Y'.gradeOf b.2) = 0 := by
  revert a b
  simp [hom_J, Y'.J_inv_eq_gradedGram, gradedGram, reindex_equiv Y'.indexEquiv]
  grind [GradeZeroPart]

end

/-- The splitting of `V` over its weight-zero part `V''` whose isotropic frame `k` consists of the
basis vectors of positive weight; `inclMatrix E u` has the basis vectors `e_{u j}` as columns. -/
def GradeZeroPart.splitting (Z : GradeZeroPart V V'' w) :
    V.Splitting V'' {i : ι // 0 < w i} where
  k := inclMatrix E (Subtype.val : {i : ι // 0 < w i} → ι)
  l := V.J⁻¹ * inclMatrix E (Subtype.val : {i // 0 < w i} → ι)
  i := Z.incl
  gram_kk := by exact Z.splitting_gram_kk
  gram_ll := by exact Z.splitting_gram_ll
  gram_lk := by exact Z.splitting_gram_lk
  gram_ii := Z.gram_incl
  gram_ik := by exact Z.splitting_gram_ik
  gram_il := by exact Z.splitting_gram_il
  card_eq := by exact Z.splitting_card_eq

/-- If `V''` is the weight-zero part of `V`, all weights are even and `Y'` has a string of even
length, then `Hom(X', V'')` is the weight-zero part of `Hom(V', V)`. -/
def GradeZeroPart.hom (Z : GradeZeroPart V V'' w) (hs' : Even s') (hw : ∀ i : ι, Even (w i)) :
    GradeZeroPart (V'.hom V) ((stdSpace E X').hom V'') fun r : ι × ι' ↦ w r.1 - Y'.gradeOf r.2 where
  index := Z.index.prodMap (.trans .inl Y'.indexEquiv.toEmbedding)
  mem_range_index r := by exact Z.hom_mem_range_index Y' hs' hw r
  incl := Z.incl ⊗ₖ inclMatrix E (Y'.indexEquiv ∘ Sum.inl)
  incl_eq_zero a b := by exact Z.hom_incl_eq_zero Y' a b
  gram_incl := by exact Z.hom_gram_incl Y'
  grade_add_eq_zero a b := by exact Z.hom_grade_add_eq_zero Y' a b

/-! ### Pairs of consecutive edges -/

/-- The adelic map (T*, T') from V' to V⁻ ⊕ V'', where T* is the adjoint of
`T = Y.stringMap Y' : V → V'` and `T' = Y'.stringMap Y'' : V' → V''`. -/
def stackedStringMap : Matrix (ι ⊕ ι'') ι' (𝔸 E) :=
  fromRows (V.formAdjoint V' (Y.stringMap Y')) (Y'.stringMap Y'')

/-- The finite part of `New.Seesaw.stackedStringMap`, in the frame coordinates of Hom(V', V⁻ ⊕ V''),
multiplied by α⁻¹. -/
def stackedStringMapFin : (ι ⊕ ι'') × ι' → 𝔸f E :=
  finCoord (V'.homAtPoint (flipSum V V'') (stackedStringMap Y Y' Y''))

omit [WeilData E] in
/-- The map `Y.stringMap Y'` kills `X` and has image in the string, so the groups of `X`, `X'` fix
it. -/
lemma inclX_mul_stringMap_mul_inclX_inv (g : G E (1 : X → ℤˣ)) (g' : G E (1 : X' → ℤˣ)) :
    V'.ratCoordMatrix (Y'.inclX g') * Y.stringMap Y' * V.ratCoordMatrix (Y.inclX g)⁻¹ =
      Y.stringMap Y' := by
  simp [← map_inv, stringMap, reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv,
    ratCoordMatrix_inclX, ← Matrix.ext_iff, Matrix.mul_apply, Matrix.one_apply]

/-- The strings of `Y`, `Y'`, `Y''` have lengths `s`, `s - 1` and `s - 1 - 1` (truncated
subtraction) with `s` odd, and `Y` and `Y'` have the same constant `genericConst`. -/
structure HasConsecutiveStrings (Y : Grading V N X s) (Y' : Grading V' N X' s')
    (Y'' : Grading V'' N X₀ s'') : Prop where
  /-- The string of `Y` has odd length. -/
  odd_length : Odd s
  /-- The string of `Y'` is one shorter than that of `Y`. -/
  length_middle : s' = s - 1
  /-- The string of `Y''` is one shorter than that of `Y'`, or both are empty. -/
  length_last : s'' = s' - 1
  /-- The gradings `Y` and `Y'` have the same constant for the generic character. -/
  c_eq : Y'.genericConst = Y.genericConst

/-- Data for two consecutive lifts Y → Y' → Y'' with consecutive strings
(`New.Seesaw.HasConsecutiveStrings`) and `card ι + card ι''` even. It identifies the grade-zero part
of V⁻ ⊕ V'' with X⁻ ⊕ X'' plus q hyperbolic planes, compatibly with U(X) × U(X₀) and with
`stackedStringMap`. -/
structure DoubleLiftData extends HasConsecutiveStrings Y Y' Y'' where
  /-- The part of grade zero of `V⁻ ⊕ V''` is the sum of hyperbolic planes indexed by `q` and of
  `I_X⁻ ⊕ I_{X''}`. -/
  zeroPart : GradeZeroPart (flipSum V V'')
    (hyperbolicSum q (flipSum (stdSpace E X) (stdSpace E X''))) (Y.gradeOf ⊕ᵥ Y''.gradeOf)
  /-- The dimensions of `V` and `V''` have even sum. -/
  even_card_add : Even (card ι + card ι'')
  /-- A homomorphism from the adelic unitary group of `I_{X₀}` to that of `I_{X''}`. -/
  embX : G (n := X₀) E 1 →* G (n := X'') E 1
  /-- The homomorphism preserves determinants. -/
  det_embX (k : G E (1 : X₀ → ℤˣ)) : (embX k).det = k.det
  /-- The inclusion of the part of grade zero intertwines `(g, k)`, acting on `V⁻ ⊕ V''` through `X`
  and `X₀`, with the element that is `1` on the planes, `g` on `X` and the image of `k` under the
  homomorphism on `X''`. -/
  intertwines (g : G E (1 : X → ℤˣ)) (k : G E (1 : X₀ → ℤˣ)) :
    fromBlocks (V.ratCoordMatrix (Y.inclX g)) 0 0 (V''.ratCoordMatrix (Y''.inclX k)) *
        zeroPart.incl.map toAdele = zeroPart.incl.map toAdele *
      (G.sum (s := hyperbolicSigns q) (1, G.sum (g.neg, embX k))).adeleMatrix
  /-- An injection of `q` into the basis indices of `V'` of grade one. -/
  gradeOne : q ↪ {l // Y'.gradeOf l = 1}
  /-- In the rows of grade zero, column `gradeOne k` of `stackedStringMap Y Y' Y''` is
  `Y'.genericConst` times the included second basis vector of the `k`-th plane. The columns outside
  the image of `gradeOne` vanish. -/
  stackedStringMap_apply (a : (q ⊕ q) ⊕ X ⊕ X'') (l : ι') :
    stackedStringMap Y Y' Y'' (zeroPart.index a) l = ∑ k : q, if l = gradeOne k then
      toAdele (zeroPart.incl (zeroPart.index a) (Sum.inl (Sum.inr k)) * Y'.genericConst) else 0

variable {X'' q Y Y' Y''}

namespace DoubleLiftData

/-! ### The finite evaluation and its equivariance -/

omit [Fintype X'] in
/-- The string of the middle grading `Y'` has even length, as `s' = s - 1` with `s` odd. -/
lemma even_length_middle (D : DoubleLiftData X'' q Y Y' Y'') : Even s' := by
  simpa only [D.length_middle] using D.odd_length.tsub_odd odd_one

omit [Fintype X'] in
/-- All grades on `V⁻ ⊕ V''` are even: the string of `Y` has odd length, and that of `Y''` has odd
length or is empty. -/
lemma even_gradeOf (D : DoubleLiftData X'' q Y Y' Y'') (i : ι ⊕ ι'') :
    Even ((Y.gradeOf ⊕ᵥ Y''.gradeOf) i) := by
  obtain ⟨h_odd, h_middle, h_last⟩ : Odd s ∧ s' = s - 1 ∧ s'' = s' - 1 :=
    ⟨D.odd_length, D.length_middle, D.length_last⟩
  revert i
  simp [reindex_equiv Y.indexEquiv, reindex_equiv Y''.indexEquiv]
  grind

/-- For a pair `D` of consecutive lifts, `Hom(X', Z)` is the part of grade zero of
`Hom(V', V⁻ ⊕ V'')`, where `Z` is the part of grade zero of `V⁻ ⊕ V''`. -/
def homZeroPart (D : DoubleLiftData X'' q Y Y' Y'') :
    GradeZeroPart (V'.hom (flipSum V V''))
      ((stdSpace E X').hom (hyperbolicSum q (flipSum (stdSpace E X) (stdSpace E X''))))
      fun r : (ι ⊕ ι'') × ι' ↦ (Y.gradeOf ⊕ᵥ Y''.gradeOf) r.1 - Y'.gradeOf r.2 :=
  D.zeroPart.hom Y' D.even_length_middle D.even_gradeOf

/-- The splitting of Hom(V', V⁻ ⊕ V'') that removes first the maps of nonzero degree, then the
maps into the hyperbolic planes, leaving Hom(X', X⁻ ⊕ X''). -/
def splitting (D : DoubleLiftData X'' q Y Y' Y'') : (V'.hom (flipSum V V'')).Splitting
    ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X'')))
    ({i : (ι ⊕ ι'') × ι' // 0 < (Y.gradeOf ⊕ᵥ Y''.gradeOf) i.1 - Y'.gradeOf i.2} ⊕ q × X') :=
  D.homZeroPart.splitting.comp ((removePlanes q _).homTarget (stdSpace E X'))

open scoped TensorProduct in
/-- The linear map on joined finite data for `Hom(V, V')` and `Hom(V', V'')`. It translates by (T*,
T'), takes the finite constant term along `New.Seesaw.DoubleLiftData.splitting`, and splits the
result by a left inverse of `arrowTensor` into data for `Hom(X, X')` and `Hom(X', X'')`. -/
def finEval (D : DoubleLiftData X'' q Y Y' Y'') : 𝒮 (V'.hom (flipSum V V'')) →ₗ[ℂ]
    ((stdSpace E X).hom (stdSpace E X')).finitePart ⊗[ℂ]
      ((stdSpace E X').hom (stdSpace E X'')).finitePart :=
  arrowTensor.leftInverse ∘ₗ
    (zeroTermFin D.splitting ∘L finHeisenbergOp _ (stackedStringMapFin Y Y' Y'')).toLinearMap

/-- `arrowTensor` applied to `D.finEval (arrowProduct Φ.val Ψ.val)` equals `zeroTermFin D.splitting`
of `arrowProduct Φ.val Ψ.val` after the finite Heisenberg operator of `stackedStringMapFin Y Y' Y''`
on `Hom(V', V⁻ ⊕ V'')` is applied to it. -/
lemma arrowTensor_finEval (D : DoubleLiftData X'' q Y Y' Y'') (Φ : (V.hom V').finitePart)
    (Ψ : (V'.hom V'').finitePart) :
    arrowTensor (D.finEval (arrowProduct Φ.val Ψ.val)) = zeroTermFin D.splitting
      ((V'.hom (flipSum V V'')).finHeisenbergOp (stackedStringMapFin Y Y' Y'')
        (arrowProduct Φ.val Ψ.val)) :=
  -- `arrowTensor.leftInverse` inverts `arrowTensor` on its range, the finite part `finitePart`,
  -- which `finHeisenbergOp` and `zeroTermFin` preserve.
  LeftInverse.rightInvOn_range leftInverse_arrowTensor <| range_arrowTensor.ge <|
    zeroTermFin_mem_finitePart D.splitting <|
      finHeisenbergOp_mem_finitePart _ (range_arrowTensor.le ⟨Φ ⊗ₜ Ψ, rfl⟩)

open Finset in
/-- Let `Z` identify `V''` with the part of weight zero of `V` for even weights `w`: `Z.incl` is the
inclusion, and `ε`, `ε''` are the signs of the two forms at the infinite places. Let `Y'` present
`V'` as the definite space on `X'` plus a string of `s'` further basis vectors, `s'` even, with
`Y'.inclX` the embedding of `U(X')` in `U(V')`. Suppose that, in rational coordinates
(`ratCoordMatrix`), `g` is the identity away from weight zero and acts as `g₀` on `V''`. Then
`Z.hom Y' hs' hw` identifies `Hom (X', V'')` with the part of weight zero of `Hom (V', V)`, and the
zero term along the resulting splitting carries the Weil operator of `(Y'.inclX h, g)` to that of
`(h, g₀)`, times `υ(det g ^ (s' / 2) * (det h)⁻¹ ^ r)⁻¹`. Here `r` is the number of indices of
positive weight and `υ` is the splitting character on the norm-one ideles (`upsilonU1`). -/
lemma _root_.New.Seesaw.GradeZeroPart.zeroTerm_hom_omega (Z : GradeZeroPart V V'' w) (hs' : Even s')
    (hw : ∀ i : ι, Even (w i)) {g : G E ε} {g₀ : G E ε''}
    (h_id : ∀ i l : ι, w i ≠ 0 ∨ w l ≠ 0 → V.ratCoordMatrix g i l = if i = l then 1 else 0)
    (h_comm : V.ratCoordMatrix g * Z.incl.map toAdele = Z.incl.map toAdele * V''.ratCoordMatrix g₀)
    (h : G E (1 : X' → ℤˣ)) (f : 𝒮 (V'.hom V)) :
    (Z.hom Y' hs' hw).splitting.zeroTerm (ω (V'.hom V) (G.onHom (Y'.inclX h, g)) f) =
      (WeilData.upsilonU1.val (g.det ^ (s' / 2) * h.det⁻¹ ^ #{i : ι | 0 < w i}) : ℂ)⁻¹ •
        ω ((stdSpace E X').hom V'') (G.onHom (h, g₀)) ((Z.hom Y' hs' hw).splitting.zeroTerm f) := by
  -- On the columns of positive weight, `G.onHom (Y'.inclX h, g)` agrees with a product `C` of two
  -- block diagonal matrices: `g` acts where the weight of `Y'` is negative, `h⁻¹` where `0 < w`.
  -- The scalar of `zeroTerm_omega_of_inclMatrix` is then the inverse of `upsilonU1` at `det C`.
  let C : Matrix (ι × ι') (ι × ι') (𝔸 E) :=
    blockDiagonal (fun l ↦ if Y'.gradeOf l < 0 then V.ratCoordMatrix g else 1) *
      (blockDiagonal fun i ↦ if 0 < w i then (V'.ratCoordMatrix (Y'.inclX h⁻¹))ᵀ
        else 1).submatrix .swap .swap
  have hC_entry (i i' : ι) (l l' : ι') :
      C (i, l) (i', l') =
        (if Y'.gradeOf l < 0 then V.ratCoordMatrix g i i' else if i = i' then 1 else 0) *
        (if 0 < w i' then V'.ratCoordMatrix (Y'.inclX h⁻¹) l' l else if l = l' then 1 else 0) := by
    dsimp only [C]
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single i']
    · rw [Finset.sum_eq_single l]
      · simp only [blockDiagonal_apply, Matrix.submatrix_apply, Prod.swap_prod_mk,
          Matrix.ite_apply, Matrix.one_apply, Matrix.transpose_apply, ↓reduceIte]
      · intro m _ hm
        simp only [blockDiagonal_apply, hm.symm, ↓reduceIte, zero_mul]
      · intro hmem; exact absurd (Finset.mem_univ l) hmem
    · intro k _ hk
      refine Finset.sum_eq_zero fun m _ ↦ ?_
      simp only [blockDiagonal_apply, Matrix.submatrix_apply, Prod.swap_prod_mk, hk, ↓reduceIte,
        mul_zero]
    · intro hmem; exact absurd (Finset.mem_univ i') hmem
  have h_h_id (l₁ l₂ : ι') (h_ne : Y'.gradeOf l₁ ≠ 0 ∨ Y'.gradeOf l₂ ≠ 0) :
      V'.ratCoordMatrix (Y'.inclX h⁻¹) l₁ l₂ = if l₁ = l₂ then 1 else 0 := by
    obtain ⟨a₁, rfl⟩ := Y'.indexEquiv.surjective l₁
    obtain ⟨a₂, rfl⟩ := Y'.indexEquiv.surjective l₂
    rw [ratCoordMatrix_inclX]
    rcases a₁ with a₁ | a₁ <;> rcases a₂ with a₂ | a₂
    · simp only [gradeOf_inl, ne_eq, not_true_eq_false, or_self] at h_ne
    · simp [gradedBlocks]
    · simp [gradedBlocks]
    · simp [gradedBlocks, Matrix.one_apply]
  refine zeroTerm_omega_of_inclMatrix (Z.hom Y' hs' hw).splitting rfl (C := C) ?_ ?_ ?_ ?_ f
  · intro ⟨i, l⟩ ⟨i', l'⟩ hdeg
    change (V'.hom V).ratCoordMatrix (G.onHom (Y'.inclX h, g)) (i, l) (i', l') -
      C (i, l) (i', l') = 0
    rw [sub_eq_zero, ratCoordMatrix_onHom, kroneckerMap_apply, Matrix.transpose_apply, ← map_inv,
      hC_entry]
    have hdeg' : Y'.gradeOf l' < w i' := by
      dsimp only [Pi.zero_apply] at hdeg; omega
    by_cases hl' : Y'.gradeOf l' = 0
    · have hwi' : 0 < w i' := by omega
      rw [ite_eq_left hwi']
      by_cases hl : Y'.gradeOf l < 0
      · rw [ite_eq_left hl]
      · rw [ite_eq_right hl]
        by_cases hl0 : Y'.gradeOf l = 0
        · rw [h_id i i' (Or.inr (by omega))]
        · have hne : l' ≠ l := fun heq ↦ hl0 (heq ▸ hl')
          rw [h_h_id l' l (Or.inr hl0), ite_eq_right hne, mul_zero, mul_zero]
    · rw [h_h_id l' l (Or.inl hl')]
      by_cases hll' : l = l'
      · subst hll'
        simp only [↓reduceIte, ite_self, mul_one]
        by_cases hl : Y'.gradeOf l < 0
        · rw [ite_eq_left hl]
        · rw [ite_eq_right hl, h_id i i' (Or.inr (by omega))]
      · have hne : l' ≠ l := Ne.symm hll'
        simp only [hll', hne, ↓reduceIte, ite_self, mul_zero]
  · intro ⟨i, l⟩ ⟨i', l'⟩ hdeg
    change C (i, l) (i', l') - (1 : Matrix (ι × ι') (ι × ι') (𝔸 E)) (i, l) (i', l') = 0
    rw [sub_eq_zero, hC_entry, Matrix.one_apply]
    have hdeg1 : w i - Y'.gradeOf l ≤ 0 := by
      dsimp only [Pi.inf_apply, Pi.zero_apply] at hdeg; omega
    have hdeg2 : w i - Y'.gradeOf l ≤ w i' - Y'.gradeOf l' := by
      dsimp only [Pi.inf_apply, Pi.zero_apply] at hdeg; omega
    have hf1 : (if Y'.gradeOf l < 0 then V.ratCoordMatrix g i i' else if i = i' then 1 else 0) =
        if i = i' then 1 else 0 := by
      by_cases hl : Y'.gradeOf l < 0
      · rw [ite_eq_left hl, h_id i i' (Or.inl (by omega))]
      · rw [ite_eq_right hl]
    rw [hf1]
    by_cases hii' : i = i'
    · subst hii'
      simp only [↓reduceIte, one_mul, Prod.mk.injEq, true_and]
      by_cases hwi : 0 < w i
      · rw [ite_eq_left hwi, h_h_id l' l (Or.inr (by omega))]
        by_cases hll' : l = l' <;> simp [hll', eq_comm]
      · rw [ite_eq_right hwi]
    · simp [hii']
  · -- The weight of `Y'` is negative at `j = s' / 2` indices.
    obtain ⟨j, rfl⟩ := hs'
    simp (disch := omega) [C, det_blockDiagonal _, ↓reindex_equiv Y'.indexEquiv, ↓prod_sum_type,
      ↓Fin.prod_univ_add, prod_ite, ite_eq_right, ← two_mul, apply_ite Matrix.det,
      det_ratCoordMatrix, ← Equiv.coe_prodComm, -inv_pow, det_inclX]
  · -- On the rows of weight `≤ 0` the embedding of the zero part intertwines, by `h_comm`.
    have h_inclX_comm : (V'.ratCoordMatrix (Y'.inclX h⁻¹))ᵀ *
        (inclMatrix E (Y'.indexEquiv ∘ Sum.inl)).map toAdele =
        (inclMatrix E (Y'.indexEquiv ∘ Sum.inl)).map toAdele *
          ((stdSpace E X').ratCoordMatrix h⁻¹)ᵀ := by
      rw [ratCoordMatrix_inclX]
      refine Matrix.ext fun l a ↦ ?_
      obtain ⟨u, rfl⟩ := Y'.indexEquiv.surjective l
      cases u <;> simp [inclMatrix, Matrix.mul_apply, Matrix.one_apply, gradedBlocks]
    have h_map : (Z.incl ⊗ₖ inclMatrix E (Y'.indexEquiv ∘ Sum.inl)).map toAdele =
        Z.incl.map toAdele ⊗ₖ (inclMatrix E (Y'.indexEquiv ∘ Sum.inl)).map toAdele :=
      Matrix.ext fun ⟨_, _⟩ ⟨_, _⟩ ↦ map_mul toAdele _ _
    have h_zero : (V'.hom V).ratCoordMatrix (G.onHom (Y'.inclX h, g)) *
        (Z.hom Y' hs' hw).splitting.i.map toAdele -
        (Z.hom Y' hs' hw).splitting.i.map toAdele *
          ((stdSpace E X').hom V'').ratCoordMatrix (G.onHom (h, g₀)) = 0 := by
      rw [ratCoordMatrix_onHom, ratCoordMatrix_onHom, GradeZeroPart.splitting, GradeZeroPart.hom]
      dsimp only
      rw [← map_inv, h_map, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, h_comm, h_inclX_comm, sub_self]
    intro a b _
    rw [h_zero]
    rfl

private lemma tripleWeil_circle_eq (ag ag' bk bg' ug ug' uk : Circle)
    {cι cι' cι'' cX cX' cX'' cq s' r : ℕ}
    (h_even_s' : Even s') (h_rank' : cX' + s' = cι')
    (h_par : Even (cι + cι''))
    (h_rank : cι + cι'' = cq + cq + (cX + cX'') + 2 * r) :
    ag' * ag⁻¹ * ug' ^ (cι / 2) * (ug ^ (cι' / 2))⁻¹ *
      (bk * bg'⁻¹ * uk ^ (cι' / 2) * (ug' ^ (cι'' / 2))⁻¹) *
      (ug ^ cι' * (ug' ^ cι)⁻¹) *
      ((ug ^ (s' / 2))⁻¹ * (uk ^ (s' / 2))⁻¹ * ug' ^ r) *
      ug' ^ cq =
    ag' * ag⁻¹ * ug' ^ (cX / 2) * (ug ^ (cX' / 2))⁻¹ *
      (bk * bg'⁻¹ * uk ^ (cX' / 2) * (ug' ^ (cX'' / 2))⁻¹) *
      (ug ^ cX' * (ug' ^ cX)⁻¹) := by
  obtain ⟨k₀, hk₀⟩ := h_even_s'
  obtain ⟨m₀, hm₀⟩ := h_par
  have h_g : (ug ^ (cι' / 2))⁻¹ * ug ^ cι' * (ug ^ (s' / 2))⁻¹ =
      (ug ^ (cX' / 2))⁻¹ * ug ^ cX' := by
    simp only [← zpow_natCast, ← _root_.zpow_neg, ← _root_.zpow_add]
    exact congrArg (ug ^ ·) (by omega)
  have h_k : uk ^ (cι' / 2) * (uk ^ (s' / 2))⁻¹ = uk ^ (cX' / 2) := by
    simp only [← zpow_natCast, ← _root_.zpow_neg, ← _root_.zpow_add]
    exact congrArg (uk ^ ·) (by omega)
  have h_g' : ug' ^ (cι / 2) * (ug' ^ (cι'' / 2))⁻¹ * (ug' ^ cι)⁻¹ * ug' ^ r * ug' ^ cq =
      ug' ^ (cX / 2) * (ug' ^ (cX'' / 2))⁻¹ * (ug' ^ cX)⁻¹ := by
    simp only [← zpow_natCast, ← _root_.zpow_neg, ← _root_.zpow_add]
    exact congrArg (ug' ^ ·) (by omega)
  calc
    ag' * ag⁻¹ * ug' ^ (cι / 2) * (ug ^ (cι' / 2))⁻¹ *
          (bk * bg'⁻¹ * uk ^ (cι' / 2) * (ug' ^ (cι'' / 2))⁻¹) *
          (ug ^ cι' * (ug' ^ cι)⁻¹) *
        ((ug ^ (s' / 2))⁻¹ * (uk ^ (s' / 2))⁻¹ * ug' ^ r) *
        ug' ^ cq
      = (ag' * ag⁻¹ * (bk * bg'⁻¹)) *
          ((ug ^ (cι' / 2))⁻¹ * ug ^ cι' * (ug ^ (s' / 2))⁻¹) *
          (uk ^ (cι' / 2) * (uk ^ (s' / 2))⁻¹) *
          (ug' ^ (cι / 2) * (ug' ^ (cι'' / 2))⁻¹ * (ug' ^ cι)⁻¹ * ug' ^ r * ug' ^ cq) := by ac_rfl
    _ = (ag' * ag⁻¹ * (bk * bg'⁻¹)) *
          ((ug ^ (cX' / 2))⁻¹ * ug ^ cX') *
          uk ^ (cX' / 2) *
          (ug' ^ (cX / 2) * (ug' ^ (cX'' / 2))⁻¹ * (ug' ^ cX)⁻¹) := by
        rw [h_g, h_k, h_g']
    _ = ag' * ag⁻¹ * ug' ^ (cX / 2) * (ug ^ (cX' / 2))⁻¹ *
          (bk * bg'⁻¹ * uk ^ (cX' / 2) * (ug' ^ (cX'' / 2))⁻¹) *
          (ug ^ cX' * (ug' ^ cX)⁻¹) := by ac_rfl

private lemma pairChar_rankTwist {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m']
    [DecidableEq m'] {sm : m → ℤˣ} {sm' : m' → ℤˣ}
    (c : AutChar E) (x : G E sm) (y : G E sm') :
    pairChar (rankTwist c m) (rankTwist c m') (x, y) =
      Circle.coeHom (c.1 y.det * (c.1 x.det)⁻¹ *
        WeilData.upsilonU1.1 y.det ^ (card m / 2) *
        (WeilData.upsilonU1.1 x.det ^ (card m' / 2))⁻¹) := by
  have hinv (φ : unitary (𝔸 E) →ₜ* Circle) (u : unitary (𝔸 E)) : φ⁻¹ u = (φ u)⁻¹ := rfl
  have h : (rankTwist c m')⁻¹.1 x.det * (rankTwist c m).1 y.det =
      c.1 y.det * (c.1 x.det)⁻¹ * WeilData.upsilonU1.1 y.det ^ (card m / 2) *
        (WeilData.upsilonU1.1 x.det ^ (card m' / 2))⁻¹ := by
    simp only [rankTwist, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_pow,
      hinv, ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.pow_apply, mul_inv]
    ac_rfl
  exact congrArg Circle.coeHom h

private lemma pairChar_upsilonU1_pow {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m']
    [DecidableEq m'] {sm : m → ℤˣ} {sm' : m' → ℤˣ}
    (x : G E sm) (y : G E sm') :
    pairChar (WeilData.upsilonU1 ^ card m) (WeilData.upsilonU1 ^ card m') (x, y) =
      Circle.coeHom (WeilData.upsilonU1.1 y.det ^ card m *
        (WeilData.upsilonU1.1 x.det ^ card m')⁻¹) := by
  have hinv (φ : unitary (𝔸 E) →ₜ* Circle) (u : unitary (𝔸 E)) : φ⁻¹ u = (φ u)⁻¹ := rfl
  have h : (WeilData.upsilonU1 ^ card m')⁻¹.1 x.det * (WeilData.upsilonU1 ^ card m).1 y.det =
      WeilData.upsilonU1.1 y.det ^ card m * (WeilData.upsilonU1.1 x.det ^ card m')⁻¹ := by
    simp only [Subgroup.coe_inv, Subgroup.coe_pow, hinv, ContinuousMonoidHom.pow_apply]
    exact mul_comm _ _
  exact congrArg Circle.coeHom h

open Finset in
/-- Let `Y`, `Y'`, `Y''` present hermitian spaces `V`, `V'`, `V''` as definite spaces on `X`, `X'`,
`X₀` plus strings of `s` (odd), `s' = s - 1` and `s'' = s - 1 - 1` further basis vectors. The data
`D` of this pair of steps identify the part of weight zero of `V⁻ ⊕ V''` with `X⁻ ⊕ X''` plus
hyperbolic planes indexed by `q`, and map `U(X₀)` to `U(X'')` by `D.embX`. For characters `a`, `b`
of `[U(1)]`, the operator `tripleWeil a b (g, g', k)` on `Hom (V', V⁻ ⊕ V'')` is the Weil operator
of `(g', g ⊕ k)` times three scalar characters: that of `(g, g')` made from `a`, that of `(g', k)`
made from `b`, and one made from the splitting character `υ` and the ranks of `V'` and `V`.

The zero term along `D.splitting`, down to `Hom (X', X⁻ ⊕ X'')`, carries this operator at
`(g, g', k)`, embedded by `inclX`, to the same operator of the definite spaces at
`(g, g', D.embX k)`, with no further scalar. -/
lemma zeroTerm_splitting_tripleWeil (D : DoubleLiftData X'' q Y Y' Y'') (a b : AutChar E)
    (g : G E (1 : X → ℤˣ)) (g' : G E (1 : X' → ℤˣ)) (k : G E (1 : X₀ → ℤˣ))
    (f : 𝒮 (V'.hom (flipSum V V''))) :
    D.splitting.zeroTerm (tripleWeil a b (Y.inclX g, Y'.inclX g', Y''.inclX k) f) =
      tripleWeil a b (g, g', D.embX k) (D.splitting.zeroTerm f) := by
  -- The constant term is taken in two stages: to the part of weight zero
  -- (`GradeZeroPart.zeroTerm_hom_omega`), then off the hyperbolic planes
  -- (`homTarget_zeroTerm_pairWeil`). Each stage gives a power of `upsilonU1`; the ranks make the
  -- exponents on both sides agree. For example, let the ranks of `V'`, `X`, `X'`, `X''` be even and
  -- those of `V`, `V''` odd, and let `χ`, `χ''` be the base changes of `a`, `b`. The splitting
  -- characters (source, target) are `(χ⁻¹, χ⁻¹ υ)` for `V' → V⁻` and `(χ'', χ'' υ⁻¹)` for
  -- `V' → V''`, but `(χ⁻¹, χ⁻¹)` for `X' → X⁻` and `(χ'', χ'')` for `X' → X''`; in the product of
  -- the characters of the targets `υ` cancels.
  let r := G.sum (g.neg, D.embX k)
  let P := removePlanes q (flipSum (stdSpace E X) (stdSpace E X''))
  let r' := G.sum (s := hyperbolicSigns q) (1, r)
  have hr' : r'.adeleMatrix =
      fromBlocks (1 : Matrix (q ⊕ q) (q ⊕ q) (𝔸 E)) 0 0 r.adeleMatrix := by
    simp only [r', G.adeleMatrix_sum, G.adeleMatrix_one]
  obtain ⟨h_k, h_i⟩ : r'.adeleMatrix * P.kAdelic = P.kAdelic ∧
      r'.adeleMatrix * P.iAdelic = P.iAdelic * r.adeleMatrix := by
    have hmap0 {α β : Type} : (0 : Matrix α β E).map toAdele = 0 :=
      Matrix.map_zero _ (RingHom.map_zero toAdele)
    have hmap1 {α : Type} [DecidableEq α] : (1 : Matrix α α E).map toAdele = 1 :=
      Matrix.map_one _ (RingHom.map_zero toAdele) (RingHom.map_one toAdele)
    constructor <;>
      simp [P, r', kAdelic, iAdelic, Space.ratMap, removePlanes, hyperbolicSum, hr', sum,
        blockGL, -coe_units_inv, fromRows_map, hmap0, hmap1, fromBlocks_mul_fromRows,
        fromBlocks_multiply]
  have h_planes : ∀ f, (P.homTarget (stdSpace E X')).zeroTerm (ω _ (.onHom (g', r')) f) =
      ((WeilData.upsilonU1.val g'.det).val : ℂ) ^ card q •
        ω _ (.onHom (g', r)) ((P.homTarget (stdSpace E X')).zeroTerm f) := by
    intro f
    have h := P.homTarget_zeroTerm_pairWeil (stdSpace E X') 1 1 r' r 1
      (by simp only [ActsOnFrame, h_k, Units.val_one, Matrix.mul_one])
      (by simp [h_i]) g' f
    simpa [pairWeil, inv_smul_eq_iff₀, r'] using h
  have h_det : (G.sum ((Y.inclX g).neg, Y''.inclX k)).det = (Y.inclX g).det * (Y''.inclX k).det :=
    Subtype.ext (by simp)
  simp only [splitting, homZeroPart, tripleWeil, _root_.smul_apply, map_smul, zeroTerm_comp]
  rw [GradeZeroPart.zeroTerm_hom_omega, h_det, map_smul, h_planes]
  · -- Only the scalars remain: the exponents of `upsilonU1` at the three determinants match by the
    -- rank formulas, as `s'` and `card ι + card ι''` are even.
    have h_rank : card (ι ⊕ ι'') = card ((q ⊕ q) ⊕ X ⊕ X'') +
        2 * card {i // 0 < (Y.gradeOf ⊕ᵥ Y''.gradeOf) i} := D.zeroPart.splitting.card_eq
    have h_rank' : card (X' ⊕ Fin s') = card ι' := card_congr Y'.indexEquiv
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_subtype] at h_rank h_rank'
    rw [smul_smul, smul_smul]
    congr 1
    rw [pairChar_rankTwist, pairChar_rankTwist, pairChar_upsilonU1_pow,
      pairChar_rankTwist, pairChar_rankTwist, pairChar_upsilonU1_pow,
      det_inclX, det_inclX, det_inclX, D.det_embX]
    have h_u1 : (WeilData.upsilonU1.val ((g.det * k.det) ^ (s' / 2) *
        g'.det⁻¹ ^ #{i | 0 < (Y.gradeOf ⊕ᵥ Y''.gradeOf) i}) : ℂ)⁻¹ =
        Circle.coeHom ((WeilData.upsilonU1.1 g.det ^ (s' / 2))⁻¹ *
          (WeilData.upsilonU1.1 k.det ^ (s' / 2))⁻¹ *
          WeilData.upsilonU1.1 g'.det ^ #{i | 0 < (Y.gradeOf ⊕ᵥ Y''.gradeOf) i}) := by
      let φ : unitary (𝔸 E) →* Circle := WeilData.upsilonU1.1.toMonoidHom
      have h : (φ ((g.det * k.det) ^ (s' / 2) *
          g'.det⁻¹ ^ #{i | 0 < (Y.gradeOf ⊕ᵥ Y''.gradeOf) i}))⁻¹ =
          (φ g.det ^ (s' / 2))⁻¹ * (φ k.det ^ (s' / 2))⁻¹ *
            φ g'.det ^ #{i | 0 < (Y.gradeOf ⊕ᵥ Y''.gradeOf) i} := by
        rw [φ.map_mul, φ.map_pow, φ.map_mul, mul_pow, φ.map_pow, φ.map_inv, inv_pow,
          mul_inv, mul_inv, inv_inv]
      exact (Circle.coeHom.map_inv _).symm.trans (congrArg Circle.coeHom h)
    have h_q : ((WeilData.upsilonU1.1 g'.det).1 : ℂ) ^ card q =
        Circle.coeHom (WeilData.upsilonU1.1 g'.det ^ card q) :=
      (Circle.coeHom.map_pow _ _).symm
    rw [h_u1, h_q]
    simp only [← Circle.coeHom.map_mul]
    exact congrArg Circle.coeHom (tripleWeil_circle_eq _ _ _ _ _ _ _
      D.even_length_middle h_rank' D.even_card_add h_rank)
  · -- The group element is the identity away from weight zero.
    intro x y hne
    rw [flipSum, ratCoordMatrix_sum]
    rcases x with x | x <;> rcases y with y | y
    · obtain ⟨u, rfl⟩ := Y.indexEquiv.surjective x
      obtain ⟨v, rfl⟩ := Y.indexEquiv.surjective y
      rcases u with u | u <;> rcases v with v | v <;>
        simp [ratCoordMatrix_inclX, gradedBlocks, Matrix.one_apply] at hne ⊢
    · simp
    · simp
    · obtain ⟨u, rfl⟩ := Y''.indexEquiv.surjective x
      obtain ⟨v, rfl⟩ := Y''.indexEquiv.surjective y
      rcases u with u | u <;> rcases v with v | v <;>
        simp [ratCoordMatrix_inclX, gradedBlocks, Matrix.one_apply] at hne ⊢
  · -- It is intertwined with `r'` by the embedding, which is `D.intertwines`.
    simp [hyperbolicSum, r', r, D.intertwines, ratCoordMatrix_sum]

/-- Let `Y`, `Y'`, `Y''` present `V`, `V'`, `V''` as definite spaces on `X`, `X'`, `X₀` plus strings
of lengths `s` (odd), `s - 1` and `s - 1 - 1`, and let the data `D` identify the part of weight zero
of `V⁻ ⊕ V''` with `X⁻ ⊕ X''` plus hyperbolic planes indexed by `q`; `D.embX` maps `U(X₀)` to
`U(X'')`. Finite data are elements of `finitePart`, the span of the finite translates of the vacuum.
`arrowProduct` joins such data `Φ` on `Hom (V, V')` and `Φ'` on `Hom (V', V'')`, and `D.finEval`
sends the result to a tensor of finite data on `Hom (X, X')` and `Hom (X', X'')`.

This evaluation is equivariant: if `Φ`, `Φ'` are moved by finite points `g, g', k` of the unitary
groups of `X, X', X₀`, embedded by `inclXFin`, then the tensor moves by `(g, g')` and `(g', k')`,
where `D.embX (1, k) = (1, k')`. -/
lemma finEval_arrowProduct_equivariant (D : DoubleLiftData X'' q Y Y' Y'') (a b : AutChar E)
    {g : Gf E X} {g' : Gf E X'} {k : Gf E X₀} {k' : Gf E X''} (hk' : D.embX (1, k) = (1, k'))
    (Φ : (V.hom V').finitePart) (Φ' : (V'.hom V'').finitePart) :
    D.finEval (arrowProduct (liftWeilFin a (Y.inclXFin g, Y'.inclXFin g') Φ).val
        (liftWeilFin b (Y'.inclXFin g', Y''.inclXFin k) Φ').val) =
      TensorProduct.map (liftWeilFin a (g, g')) (liftWeilFin b (g', k'))
        (D.finEval (arrowProduct Φ.val Φ'.val)) := by
  -- Apply `arrowTensor` to the right side and move `tripleWeil` inside the constant term
  -- (`zeroTerm_splitting_tripleWeil`). There it passes `integrated` and the translation by
  -- `stackedStringMapFin`, because the elements `inclX` fix `Y.stringMap Y'` and `Y'.stringMap Y''`
  -- (`inclX_mul_stringMap_mul_inclX_inv`).
  let W := tripleWeil (V := V) (V' := V') (V'' := V'') a b
    (Y.inclX (1, g), Y'.inclX (1, g'), Y''.inclX (1, k))
  -- These elements have trivial real part, so they do not move a Fock vector `v`.
  have h_comm (v f) : W ((V'.hom (flipSum V V'')).integrated v f) =
      (V'.hom (flipSum V V'')).integrated v (W f) := by
    simp [W, tripleWeil, omega_integrated, inclX_inr, G.onHom_eq, G.sum, G.neg, ← Pi.one_def,
      MulEquiv.prodCongr, Prod.mk_one_one]
  -- Hence the finite constant term, too, carries `W` to the operator of the definite spaces.
  have h_equivariant (f : 𝒮 (V'.hom (flipSum V V''))) :
      tripleWeil a b ((1, g), (1, g'), 1, k') (zeroTermFin D.splitting f) =
        zeroTermFin D.splitting (W f) := by
    simp [zeroTermFin, ← h_comm, W, D.zeroTerm_splitting_tripleWeil, hk']
  -- The adelic point of `stackedStringMapFin` is the pair of the finite parts of `Y.stringMap Y'`
  -- and `Y'.stringMap Y''`.
  have h_point : finVec (stackedStringMapFin Y Y' Y'') = V'.homAtPoint (flipSum V V'')
      (fromRows (V.formAdjoint V' (((0, 1) : 𝔸 E) • Y.stringMap Y'))
        (((0, 1) : 𝔸 E) • Y'.stringMap Y'')) := by
    have h_mat : fromRows (V.formAdjoint V' (((0, 1) : 𝔸 E) • Y.stringMap Y'))
        (((0, 1) : 𝔸 E) • Y'.stringMap Y'') =
        ((0, 1) : 𝔸 E) • stackedStringMap Y Y' Y'' := by
      have h_adj : V.formAdjoint V' (((0, 1) : 𝔸 E) • Y.stringMap Y') =
          ((0, 1) : 𝔸 E) • V.formAdjoint V' (Y.stringMap Y') := by
        simp only [formAdjoint, Matrix.conjTranspose_smul, Prod.star_def, star_zero, star_one,
          Matrix.mul_smul, Matrix.smul_mul]
      rw [h_adj, stackedStringMap]
      refine Matrix.ext fun a b ↦ ?_
      cases a <;> rfl
    rw [h_mat]
    funext p
    have h_smul : V'.homAtPoint (flipSum V V'') (((0, 1) : 𝔸 E) • stackedStringMap Y Y' Y'') p =
        ((0, 1) : 𝔸 E) * V'.homAtPoint (flipSum V V'') (stackedStringMap Y Y' Y'') p := by
      change ((flipSum V V'').x⁻¹.val * (((0, 1) : 𝔸 E) • stackedStringMap Y Y' Y'') *
        V'.x.val) p.1 p.2 = _
      rw [Matrix.mul_smul, Matrix.smul_mul]
      rfl
    rw [h_smul]
    apply Prod.ext
    · simp only [finVec, Prod.fst_mul, zero_mul]
    · simp only [finVec, stackedStringMapFin, finCoord, ← mul_assoc, Units.mul_inv,
        Prod.snd_mul, one_mul]
  rw [← leftInverse_arrowTensor (TensorProduct.map _ _ _), arrowTensor_map_liftWeilFin,
    arrowTensor_finEval, h_equivariant]
  -- Split the translation over the two factors (`homHeisenbergOp_arrowProduct`,
  -- `arrowProduct_twistedPairWeil`) and commute on each (`pairWeil_homHeisenbergOp`).
  simp [W, finEval, finHeisenbergOp, h_point, homHeisenbergOp_arrowProduct, ← inclX_inr,
    ← arrowProduct_twistedPairWeil, pairWeil_homHeisenbergOp, inclX_mul_stringMap_mul_inclX_inv]

end DoubleLiftData

variable (Y Y' Y'')

/-! ### The two kinds of pairs -/

omit [Fintype X] [Fintype X₀] in
private lemma flipSum_grade_add_eq_zero (a b : ι ⊕ ι'') :
    (flipSum V V'').J a b ≠ 0 → (Y.gradeOf ⊕ᵥ Y''.gradeOf) a + (Y.gradeOf ⊕ᵥ Y''.gradeOf) b = 0 := by
  revert a b
  simp [↓reindex_equiv Y.indexEquiv, ↓reindex_equiv Y''.indexEquiv, Y.gram_eq, Y''.gram_eq,
    flipSpace, gradedGram]
  grind

omit [WeilData E] [Fintype X] [Fintype X'] [Fintype X₀] in
private lemma middleDoubleLift_mem_range_index (h_string : HasConsecutiveStrings Y Y' Y'')
    (hz : s / 2 < s) (hz' : s'' / 2 < s'') (incl : ι ⊕ ι'') :
    incl ∈ Set.range ((fun _ : Unit ↦ Sum.inl (Y.indexEquiv (Sum.inr ⟨s / 2, hz⟩))) ⊕ᵥ
        (fun _ : Unit ↦ Sum.inr (Y''.indexEquiv (Sum.inr ⟨s'' / 2, hz'⟩))) ⊕ᵥ
        Sum.map (Y.indexEquiv ∘ Sum.inl) (Y''.indexEquiv ∘ Sum.inl)) ↔
      (Y.gradeOf ⊕ᵥ Y''.gradeOf) incl = 0 := by
  have h_odd : Odd s := h_string.odd_length
  have h_middle : s' = s - 1 := h_string.length_middle
  have h_last : s'' = s' - 1 := h_string.length_last
  revert incl
  simp [↓reindex_equiv Y.indexEquiv, ↓reindex_equiv Y''.indexEquiv, Fin.ext_iff, sub_eq_zero]
  grind

omit [WeilData E] [Fintype X] [Fintype X'] [Fintype X₀] in
private lemma middleDoubleLift_incl_eq_zero (h_string : HasConsecutiveStrings Y Y' Y'')
    (hz : s / 2 < s) (hz' : s'' / 2 < s'')
    (a : ι ⊕ ι'') (b : (Unit ⊕ Unit) ⊕ X ⊕ X₀) :
    (Y.gradeOf ⊕ᵥ Y''.gradeOf) a ≠ 0 →
      (fromCols (fromCols ((2 * N)⁻¹ •
          (inclMatrix E (fun _ : Unit ↦ Sum.inl (Y.indexEquiv (Sum.inr ⟨s / 2, hz⟩))) -
            inclMatrix E (fun _ : Unit ↦ Sum.inr (Y''.indexEquiv (Sum.inr ⟨s'' / 2, hz'⟩)))))
        (inclMatrix E (fun _ : Unit ↦ Sum.inl (Y.indexEquiv (Sum.inr ⟨s / 2, hz⟩))) +
          inclMatrix E (fun _ : Unit ↦ Sum.inr (Y''.indexEquiv (Sum.inr ⟨s'' / 2, hz'⟩)))))
        (inclMatrix E (Sum.map (Y.indexEquiv ∘ Sum.inl) (Y''.indexEquiv ∘ Sum.inl)))) a b = 0 := by
  have h_odd : Odd s := h_string.odd_length
  have h_middle : s' = s - 1 := h_string.length_middle
  have h_last : s'' = s' - 1 := h_string.length_last
  revert a b
  simp [↓reindex_equiv Y.indexEquiv, ↓reindex_equiv Y''.indexEquiv, inclMatrix, Matrix.one_apply,
    sub_eq_zero]
  grind

omit [Fintype X'] in
private lemma middleDoubleLift_gram_incl (h_string : HasConsecutiveStrings Y Y' Y'')
    (hz : s / 2 < s) (hz' : s'' / 2 < s'') :
    let z (_ : Unit) : ι ⊕ ι'' := Sum.inl (Y.indexEquiv (Sum.inr ⟨s / 2, hz⟩))
    let z' (_ : Unit) : ι ⊕ ι'' := Sum.inr (Y''.indexEquiv (Sum.inr ⟨s'' / 2, hz'⟩))
    let j := Sum.map (Y.indexEquiv ∘ Sum.inl) (Y''.indexEquiv ∘ Sum.inl)
    let A := fromCols (fromCols ((2 * N)⁻¹ • (inclMatrix E z - inclMatrix E z'))
      (inclMatrix E z + inclMatrix E z')) (inclMatrix E j)
    Aᴴ * (flipSum V V'').J * A =
      (hyperbolicSum Unit (flipSum (stdSpace E X) (stdSpace E X₀))).J := by
  intro z z' j A
  have h_odd : Odd s := h_string.odd_length
  have h_middle : s' = s - 1 := h_string.length_middle
  have h_last : s'' = s' - 1 := h_string.length_last
  have h_imm {α γ : Type} (f : α → ι ⊕ ι'') (g : γ → ι ⊕ ι'') (a : α) (b : γ) :
      ((inclMatrix E f)ᴴ * (flipSum V V'').J * inclMatrix E g) a b =
        (flipSum V V'').J (f a) (g b) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, inclMatrix,
      Matrix.submatrix_apply, id_eq, Matrix.one_apply, apply_ite star, star_one, star_zero,
      ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
  have h_starN : star N = N := Y.N_ne_zero_and_star_eq.2
  have h_Nne : N ≠ 0 := Y.N_ne_zero_and_star_eq.1
  have hJ_zz : (flipSum V V'').J (z ()) (z ()) = N := by
    have hrev : (⟨s / 2, hz⟩ : Fin s).rev = ⟨s / 2, hz⟩ := by
      obtain ⟨k, hk⟩ := h_odd
      exact Fin.ext (by dsimp [Fin.rev]; omega)
    simp [z, flipSpace, Y.gram_eq, gradedGram, gradedBlocks, hrev]
  have hJ_z'z' : (flipSum V V'').J (z' ()) (z' ()) = -N := by
    have hrev : (⟨s'' / 2, hz'⟩ : Fin s'').rev = ⟨s'' / 2, hz'⟩ := by
      obtain ⟨k, hk⟩ := h_odd
      exact Fin.ext (by dsimp [Fin.rev]; omega)
    simp [z', flipSpace, Y''.gram_eq, gradedGram, gradedBlocks, hrev]
  have hJ_zz' : (flipSum V V'').J (z ()) (z' ()) = 0 := by simp [z, z', flipSpace]
  have hJ_z'z : (flipSum V V'').J (z' ()) (z ()) = 0 := by simp [z, z', flipSpace]
  have hJ_zj (x : X ⊕ X₀) : (flipSum V V'').J (z ()) (j x) = 0 := by
    cases x <;> simp [z, j, flipSpace, Y.gram_eq, gradedGram, gradedBlocks]
  have hJ_jz (x : X ⊕ X₀) : (flipSum V V'').J (j x) (z ()) = 0 := by
    cases x <;> simp [z, j, flipSpace, Y.gram_eq, gradedGram, gradedBlocks]
  have hJ_z'j (x : X ⊕ X₀) : (flipSum V V'').J (z' ()) (j x) = 0 := by
    cases x <;> simp [z', j, flipSpace, Y''.gram_eq, gradedGram, gradedBlocks]
  have hJ_jz' (x : X ⊕ X₀) : (flipSum V V'').J (j x) (z' ()) = 0 := by
    cases x <;> simp [z', j, flipSpace, Y''.gram_eq, gradedGram, gradedBlocks]
  have hJ_jj (x y : X ⊕ X₀) :
      (flipSum V V'').J (j x) (j y) = (flipSum (stdSpace E X) (stdSpace E X₀)).J x y := by
    cases x <;> cases y <;>
      simp [j, flipSpace, Y.gram_eq, Y''.gram_eq, gradedGram, gradedBlocks, Matrix.one_apply]
  let J := (flipSum V V'').J
  let Ez := inclMatrix E z
  let Ez' := inclMatrix E z'
  let Ej := inclMatrix E j
  let A₁ := (2 * N)⁻¹ • (Ez - Ez')
  let A₂ := Ez + Ez'
  have h11 : A₁ᴴ * J * A₁ = 0 := by
    refine Matrix.ext fun () () ↦ ?_
    simp only [A₁, Ez, Ez', J, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.zero_apply, h_imm, hJ_zz, hJ_z'z', hJ_zz', hJ_z'z]
    ring
  have h12 : A₁ᴴ * J * A₂ = 1 := by
    refine Matrix.ext fun () () ↦ ?_
    simp only [A₁, A₂, Ez, Ez', J, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.smul_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.one_apply_eq, h_imm, hJ_zz, hJ_z'z', hJ_zz', hJ_z'z,
      star_inv₀, star_mul', star_ofNat, h_starN, smul_eq_mul]
    field_simp [h_Nne]
    ring
  have h21 : A₂ᴴ * J * A₁ = 1 := by
    refine Matrix.ext fun () () ↦ ?_
    simp only [A₁, A₂, Ez, Ez', J, Matrix.conjTranspose_add, Matrix.mul_smul,
      Matrix.add_mul, Matrix.mul_sub, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.one_apply_eq, h_imm, hJ_zz, hJ_z'z', hJ_zz', hJ_z'z, smul_eq_mul]
    field_simp [h_Nne]
    ring
  have h22 : A₂ᴴ * J * A₂ = 0 := by
    refine Matrix.ext fun () () ↦ ?_
    simp only [A₂, Ez, Ez', J, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
      Matrix.add_apply, Matrix.zero_apply, h_imm, hJ_zz, hJ_z'z', hJ_zz', hJ_z'z]
    ring
  have h13 : A₁ᴴ * J * Ej = 0 := by
    refine Matrix.ext fun () x ↦ ?_
    simp only [A₁, Ez, Ez', Ej, J, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.smul_mul, Matrix.sub_mul, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.zero_apply, h_imm, hJ_zj, hJ_z'j, sub_self, smul_zero]
  have h23 : A₂ᴴ * J * Ej = 0 := by
    refine Matrix.ext fun () x ↦ ?_
    simp only [A₂, Ez, Ez', Ej, J, Matrix.conjTranspose_add, Matrix.add_mul,
      Matrix.add_apply, Matrix.zero_apply, h_imm, hJ_zj, hJ_z'j, add_zero]
  have h31 : Ejᴴ * J * A₁ = 0 := by
    refine Matrix.ext fun x () ↦ ?_
    simp only [A₁, Ez, Ez', Ej, J, Matrix.mul_smul, Matrix.mul_sub, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.zero_apply, h_imm, hJ_jz, hJ_jz', sub_self, smul_zero]
  have h32 : Ejᴴ * J * A₂ = 0 := by
    refine Matrix.ext fun x () ↦ ?_
    simp only [A₂, Ez, Ez', Ej, J, Matrix.mul_add, Matrix.add_apply, Matrix.zero_apply,
      h_imm, hJ_jz, hJ_jz', add_zero]
  have h33 : Ejᴴ * J * Ej = (flipSum (stdSpace E X) (stdSpace E X₀)).J :=
    Matrix.ext fun x y ↦ (h_imm j j x y).trans (hJ_jj x y)
  change (fromCols (fromCols A₁ A₂) Ej)ᴴ * J * fromCols (fromCols A₁ A₂) Ej = _
  simp only [conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul,
    Matrix.mul_fromCols, h11, h12, h21, h22, h13, h23, h31, h32, h33]
  refine Matrix.ext fun a b ↦ ?_
  rcases a with (⟨⟩ | ⟨⟩) | a <;> rcases b with (⟨⟩ | ⟨⟩) | b <;>
    simp [hyperbolicSum]

omit [WeilData E] in
private lemma middleDoubleLift_intertwines (hz : s / 2 < s) (hz' : s'' / 2 < s'')
    (g : G E (1 : X → ℤˣ)) (k : G E (1 : X₀ → ℤˣ)) :
    let z (_ : Unit) : ι ⊕ ι'' := Sum.inl (Y.indexEquiv (Sum.inr ⟨s / 2, hz⟩))
    let z' (_ : Unit) : ι ⊕ ι'' := Sum.inr (Y''.indexEquiv (Sum.inr ⟨s'' / 2, hz'⟩))
    let j := Sum.map (Y.indexEquiv ∘ Sum.inl) (Y''.indexEquiv ∘ Sum.inl)
    let A := fromCols (fromCols ((2 * N)⁻¹ • (inclMatrix E z - inclMatrix E z'))
      (inclMatrix E z + inclMatrix E z')) (inclMatrix E j)
    fromBlocks (V.ratCoordMatrix (Y.inclX g)) 0 0 (V''.ratCoordMatrix (Y''.inclX k)) *
        A.map toAdele =
      A.map toAdele * (G.sum (s := hyperbolicSigns Unit) (1, G.sum (g.neg, k))).adeleMatrix := by
  intro z z' j A
  set M := fromBlocks (V.ratCoordMatrix (Y.inclX g)) 0 0 (V''.ratCoordMatrix (Y''.inclX k))
  have hM_mul {α : Type} (f : α → ι ⊕ ι'') (a : ι ⊕ ι'') (b : α) :
      (M * (inclMatrix E f).map toAdele) a b = M a (f b) := by
    simp only [Matrix.mul_apply, Matrix.map_apply, inclMatrix, Matrix.submatrix_apply, id_eq,
      Matrix.one_apply, apply_ite toAdele, map_one, map_zero, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hM_z : M * (inclMatrix E z).map toAdele = (inclMatrix E z).map toAdele := by
    refine Matrix.ext fun a () ↦ ?_
    rw [hM_mul]
    rcases a with a | a
    · obtain ⟨u, rfl⟩ := Y.indexEquiv.surjective a
      cases u <;> simp [M, z, ratCoordMatrix_inclX, gradedBlocks, inclMatrix, Matrix.one_apply]
    · simp [M, z, inclMatrix]
  have hM_z' : M * (inclMatrix E z').map toAdele = (inclMatrix E z').map toAdele := by
    refine Matrix.ext fun a () ↦ ?_
    rw [hM_mul]
    rcases a with a | a
    · simp [M, z', inclMatrix]
    · obtain ⟨u, rfl⟩ := Y''.indexEquiv.surjective a
      cases u <;> simp [M, z', ratCoordMatrix_inclX, gradedBlocks, inclMatrix, Matrix.one_apply]
  have hM_j : M * (inclMatrix E j).map toAdele =
      (inclMatrix E j).map toAdele * (G.sum (g.neg, k)).adeleMatrix := by
    refine Matrix.ext fun a b ↦ ?_
    rw [hM_mul]
    rcases a with a | a <;> rcases b with b | b
    · obtain ⟨u, rfl⟩ := Y.indexEquiv.surjective a
      cases u <;> simp [M, j, ratCoordMatrix_inclX, gradedBlocks, inclMatrix, Matrix.mul_apply,
        Matrix.one_apply]
    · simp [M, j, inclMatrix, Matrix.mul_apply, Matrix.one_apply]
    · simp [M, j, inclMatrix, Matrix.mul_apply, Matrix.one_apply]
    · obtain ⟨u, rfl⟩ := Y''.indexEquiv.surjective a
      cases u <;> simp [M, j, ratCoordMatrix_inclX, gradedBlocks, inclMatrix, Matrix.mul_apply,
        Matrix.one_apply]
  have h_rhs : (G.sum (s := hyperbolicSigns Unit) (1, G.sum (g.neg, k))).adeleMatrix =
      fromBlocks (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) (𝔸 E)) 0 0
        (G.sum (g.neg, k)).adeleMatrix := by
    simp
  have h_map_A₁ : ((2 * N)⁻¹ • (inclMatrix E z - inclMatrix E z')).map toAdele =
      toAdele (2 * N)⁻¹ • ((inclMatrix E z).map toAdele - (inclMatrix E z').map toAdele) :=
    Matrix.ext fun _ _ ↦ by simp
  have h_map_A₂ : (inclMatrix E z + inclMatrix E z').map toAdele =
      (inclMatrix E z).map toAdele + (inclMatrix E z').map toAdele :=
    Matrix.ext fun _ _ ↦ map_add toAdele _ _
  dsimp only [A]
  rw [h_rhs, fromCols_map, fromCols_map, h_map_A₁, h_map_A₂, Matrix.mul_fromCols,
    Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, Matrix.mul_one, Matrix.mul_zero,
    Matrix.mul_zero, add_zero, zero_add, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_add,
    hM_z, hM_z', hM_j]

omit [WeilData E] [Fintype X₀] in
private lemma middleDoubleLift_stackedStringMap_apply (h_string : HasConsecutiveStrings Y Y' Y'')
    (hz : s / 2 < s) (hz' : s'' / 2 < s'') (hg : s'' / 2 < s')
    (a : (Unit ⊕ Unit) ⊕ X ⊕ X₀) (l : ι') :
    let z (_ : Unit) : ι ⊕ ι'' := Sum.inl (Y.indexEquiv (Sum.inr ⟨s / 2, hz⟩))
    let z' (_ : Unit) : ι ⊕ ι'' := Sum.inr (Y''.indexEquiv (Sum.inr ⟨s'' / 2, hz'⟩))
    let j := Sum.map (Y.indexEquiv ∘ Sum.inl) (Y''.indexEquiv ∘ Sum.inl)
    let A := fromCols (fromCols ((2 * N)⁻¹ • (inclMatrix E z - inclMatrix E z'))
      (inclMatrix E z + inclMatrix E z')) (inclMatrix E j)
    stackedStringMap Y Y' Y'' ((z ⊕ᵥ z' ⊕ᵥ j) a) l =
      ∑ k : Unit, if l = Y'.indexEquiv (Sum.inr ⟨s'' / 2, hg⟩) then
        toAdele (A ((z ⊕ᵥ z' ⊕ᵥ j) a) (Sum.inl (Sum.inr k)) * Y'.genericConst) else 0 := by
  intro z z' j A
  have h_odd : Odd s := h_string.odd_length
  have h_middle : s' = s - 1 := h_string.length_middle
  have h_last : s'' = s' - 1 := h_string.length_last
  have h_const : Y'.genericConst = Y.genericConst := h_string.c_eq
  have h_starN : star N = N := Y.N_ne_zero_and_star_eq.2
  have h_Nne : N ≠ 0 := Y.N_ne_zero_and_star_eq.1
  have h0 : toAdele (0 : E) = 0 := RingHom.map_zero toAdele
  obtain ⟨k₀, hk₀⟩ := h_string.odd_length
  obtain ⟨u, rfl⟩ := Y'.indexEquiv.surjective l
  rcases a with (⟨⟩ | ⟨⟩) | x | x₀ <;> rcases u with u | u
  · simp [z, stackedStringMap, Y.formAdjoint_apply Y', stringMap, gradedBlocks,
      stringReversal, h0]
  · have hrev_z : (⟨s / 2, hz⟩ : Fin s).rev = ⟨s / 2, hz⟩ :=
      Fin.ext (by dsimp [Fin.rev]; omega)
    have hrev_u : (u.rev : ℕ) = s / 2 ↔ (u : ℕ) = s'' / 2 := by
      dsimp [Fin.rev]; omega
    simp only [Sum.elim_inl, stackedStringMap, fromRows_apply_inl,
      Y.formAdjoint_apply Y', stringMap, stringReversal, gradedGram, gradedBlocks,
      Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Sum.map_inr,
      fromBlocks_apply₂₂, Matrix.of_apply, Equiv.apply_eq_iff_eq, Sum.inr.injEq, Fin.ext_iff,
      Finset.univ_unique, Finset.sum_singleton, z, z', A, fromCols_apply_inl,
      fromCols_apply_inr, Matrix.add_apply, inclMatrix, Matrix.one_apply, id_eq, hrev_z, hrev_u,
      h_const, reduceCtorEq, ↓reduceIte, add_zero, one_mul]
    by_cases hu : (u : ℕ) = s'' / 2
    · have h2 : 2 * (s / 2) + 1 = s := by omega
      have hiff : ¬(Odd s ↔ s < s) := by simp [h_odd]
      have h_eq : (u.rev : ℕ) ≠ s'' / 2 := by dsimp [Fin.rev]; omega
      simp only [hu, ↓reduceIte, h2, star_toAdele, ← RingHom.map_mul]
      refine congrArg toAdele ?_
      have h_star_c : star (Y.genericConst : E) = Y.genericConst := Y.genericConst.2.2
      simp only [star_mul', star_neg, h_starN]
      rw [ite_eq_right hiff, ite_eq_right h_eq, h_star_c]
      field_simp [h_Nne]
    · simp only [hu, ↓reduceIte, h0, star_zero, mul_zero, zero_mul]
  · simp [z', stackedStringMap, stringMap, gradedBlocks, h0]
  · simp only [Sum.elim_inl, Sum.elim_inr, stackedStringMap, fromRows_apply_inr,
      stringMap, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      fromBlocks_apply₂₂, Matrix.of_apply, Equiv.apply_eq_iff_eq, Sum.inr.injEq,
      Fin.ext_iff, Finset.univ_unique, Finset.sum_singleton, z, z', A,
      fromCols_apply_inl, fromCols_apply_inr, Matrix.add_apply, inclMatrix,
      Matrix.one_apply, id_eq, reduceCtorEq, ↓reduceIte, zero_add, one_mul]
    by_cases hu : (u : ℕ) = s'' / 2
    · have h1 : 2 * (s'' / 2) + 1 ≠ s' := by omega
      have h2 : ¬(Odd s' ↔ 2 * (s'' / 2) + 1 < s') := by
        have hlt : 2 * (s'' / 2) + 1 < s' := by omega
        have hev : ¬Odd s' := by rw [Nat.not_odd_iff_even]; exact ⟨k₀, by omega⟩
        simp [hlt, hev]
      simp only [hu, ↓reduceIte, h1, h2, mul_one]
    · have hu' : s'' / 2 ≠ (u : ℕ) := Ne.symm hu
      simp only [hu, hu', ↓reduceIte, h0]
  · simp [j, z, z', stackedStringMap, Y.formAdjoint_apply Y', stringMap, gradedBlocks,
      stringReversal, h0]
  · simp [A, j, z, z', stackedStringMap, Y.formAdjoint_apply Y', stringMap, gradedBlocks,
      stringReversal, inclMatrix, h0]
  · simp [j, z, z', stackedStringMap, stringMap, gradedBlocks, h0]
  · simp [A, j, z, z', stackedStringMap, stringMap, gradedBlocks, inclMatrix, h0]

/-- The pair data for strings of lengths s (odd, s ≠ 1), s − 1 and s − 2, with
`Y'.genericConst = Y.genericConst` and `card ι + card ι''` even: one hyperbolic plane, spanned by
the middle vectors z of Y and z' of Y'', is removed. -/
def middleDoubleLift (h_string : HasConsecutiveStrings Y Y' Y'') (h_card : Even (card ι + card ι''))
    (hs : s ≠ 1) : DoubleLiftData X₀ Unit Y Y' Y'' :=
  have h_odd : Odd s := h_string.odd_length
  have h_middle : s' = s - 1 := h_string.length_middle
  have h_last : s'' = s' - 1 := h_string.length_last
  have hz : s / 2 < s := by obtain ⟨k, hk⟩ := h_odd; omega
  have hz' : s'' / 2 < s'' := by obtain ⟨k, hk⟩ := h_odd; omega
  have hg : s'' / 2 < s' := by obtain ⟨k, hk⟩ := h_odd; omega
  -- `z` and `z'` are the middle string vectors of `V` and `V''`; `j` lists `X` and `X₀`.
  let z (_ : Unit) : ι ⊕ ι'' := Sum.inl (Y.indexEquiv (Sum.inr ⟨s / 2, hz⟩))
  let z' (_ : Unit) : ι ⊕ ι'' := Sum.inr (Y''.indexEquiv (Sum.inr ⟨s'' / 2, hz'⟩))
  let j := Sum.map (Y.indexEquiv ∘ Sum.inl) (Y''.indexEquiv ∘ Sum.inl)
  { zeroPart :=
      { index := ⟨z ⊕ᵥ z' ⊕ᵥ j, by simp [j, z, z', Injective]⟩
        mem_range_index incl := by
          exact middleDoubleLift_mem_range_index Y Y' Y'' h_string hz hz' incl
        -- The hyperbolic plane has the basis `(z - z') / (2 N)`, `z + z'`.
        incl := fromCols (fromCols ((2 * N)⁻¹ • (inclMatrix E z - inclMatrix E z'))
          (inclMatrix E z + inclMatrix E z')) (inclMatrix E j)
        incl_eq_zero a b := by
          exact middleDoubleLift_incl_eq_zero Y Y' Y'' h_string hz hz' a b
        -- `z` has norm `N` in `V⁻` and `z'` has norm `-N`.
        gram_incl := by
          exact middleDoubleLift_gram_incl Y Y' Y'' h_string hz hz'
        grade_add_eq_zero a b := by exact flipSum_grade_add_eq_zero Y Y'' a b }
    toHasConsecutiveStrings := h_string
    even_card_add := h_card
    embX := MonoidHom.id (G E (1 : X₀ → ℤˣ))
    det_embX := by simp
    intertwines g k := by exact middleDoubleLift_intertwines Y Y'' hz hz' g k
    gradeOne := ⟨fun _ ↦ ⟨Y'.indexEquiv (Sum.inr ⟨s'' / 2, hg⟩), by
        simp only [gradeOf, Equiv.symm_apply_apply, Sum.elim_inr]
        obtain ⟨k, hk⟩ := h_odd; omega⟩,
      by simp [Injective]⟩
    stackedStringMap_apply a l := by
      exact middleDoubleLift_stackedStringMap_apply Y Y' Y'' h_string hz hz' hg a l }

omit [WeilData E] [Fintype X] [Fintype X'] [Fintype X₀] in
private lemma lastDoubleLift_mem_range_index (h_string : HasConsecutiveStrings Y Y' Y'')
    (hs : s = 1) (incl : ι ⊕ ι'') :
    let j := (isEmptyElim : Empty ⊕ Empty → ι ⊕ ι'') ⊕ᵥ (Sum.inl ∘ Y.indexEquiv ∘ Sum.inl ⊕ᵥ
      (Sum.inr ∘ Y''.indexEquiv ∘ Sum.inl ⊕ᵥ
        fun _ : Unit ↦ Sum.inl (Y.indexEquiv (Sum.inr ⟨0, hs.ge⟩))))
    incl ∈ Set.range j ↔ (Y.gradeOf ⊕ᵥ Y''.gradeOf) incl = 0 := by
  have h_middle : s' = s - 1 := h_string.length_middle
  have h_last : s'' = s' - 1 := h_string.length_last
  revert incl
  simp [↓reindex_equiv Y.indexEquiv, ↓reindex_equiv Y''.indexEquiv, sub_eq_zero]
  grind

omit [WeilData E] [Fintype X] [Fintype X'] [Fintype X₀] in
private lemma lastDoubleLift_incl_eq_zero (h_string : HasConsecutiveStrings Y Y' Y'')
    (hs : s = 1) (a : ι ⊕ ι'') (b : (Empty ⊕ Empty) ⊕ X ⊕ X₀ ⊕ Unit) :
    let j := (isEmptyElim : Empty ⊕ Empty → ι ⊕ ι'') ⊕ᵥ (Sum.inl ∘ Y.indexEquiv ∘ Sum.inl ⊕ᵥ
      (Sum.inr ∘ Y''.indexEquiv ∘ Sum.inl ⊕ᵥ
        fun _ : Unit ↦ Sum.inl (Y.indexEquiv (Sum.inr ⟨0, hs.ge⟩))))
    (Y.gradeOf ⊕ᵥ Y''.gradeOf) a ≠ 0 →
      (of fun a b ↦ if a = j b then if b = Sum.inr (Sum.inr (Sum.inr ())) then p⁻¹ else 1 else 0)
        a b = 0 := by
  have h_middle : s' = s - 1 := h_string.length_middle
  have h_last : s'' = s' - 1 := h_string.length_last
  revert a b
  simp [↓reindex_equiv Y.indexEquiv, ↓reindex_equiv Y''.indexEquiv, sub_eq_zero]
  grind

private lemma lastDoubleLift_gram_incl (hp : p * star p = N) (hs : s = 1) :
    let j := (isEmptyElim : Empty ⊕ Empty → ι ⊕ ι'') ⊕ᵥ (Sum.inl ∘ Y.indexEquiv ∘ Sum.inl ⊕ᵥ
      (Sum.inr ∘ Y''.indexEquiv ∘ Sum.inl ⊕ᵥ
        fun _ : Unit ↦ Sum.inl (Y.indexEquiv (Sum.inr ⟨0, hs.ge⟩))))
    let A : Matrix (ι ⊕ ι'') ((Empty ⊕ Empty) ⊕ X ⊕ X₀ ⊕ Unit) E :=
      of fun a b ↦ if a = j b then if b = Sum.inr (Sum.inr (Sum.inr ())) then p⁻¹ else 1 else 0
    Aᴴ * (flipSum V V'').J * A =
      (hyperbolicSum Empty (flipSum (stdSpace E X) (stdSpace E (X₀ ⊕ Unit)))).J := by
  intro j A
  let c : (Empty ⊕ Empty) ⊕ X ⊕ X₀ ⊕ Unit → E :=
    fun b ↦ if b = Sum.inr (Sum.inr (Sum.inr ())) then p⁻¹ else 1
  have h_entry (a b : (Empty ⊕ Empty) ⊕ X ⊕ X₀ ⊕ Unit) :
      ((of fun r c' ↦ if r = j c' then c c' else 0)ᴴ * (flipSum V V'').J *
        (of fun r c' ↦ if r = j c' then c c' else 0)) a b =
        star (c a) * (flipSum V V'').J (j a) (j b) * c b := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      apply_ite star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  refine Matrix.ext fun a b ↦ ?_
  change ((of fun r c' ↦ if r = j c' then c c' else 0)ᴴ * (flipSum V V'').J *
    (of fun r c' ↦ if r = j c' then c c' else 0)) a b = _
  rw [h_entry]
  rcases a with (e | e) | a | a | ⟨⟩
  · exact e.elim
  · exact e.elim
  · rcases b with (e | e) | b | b | ⟨⟩
    · exact e.elim
    · exact e.elim
    · simp [c, j, flipSpace, Y.gram_eq, gradedGram, gradedBlocks, hyperbolicSum,
        Matrix.one_apply]
    · simp [c, j, flipSpace, hyperbolicSum]
    · simp [c, j, flipSpace, Y.gram_eq, gradedGram, gradedBlocks, hyperbolicSum]
  · rcases b with (e | e) | b | b | ⟨⟩
    · exact e.elim
    · exact e.elim
    · simp [c, j, flipSpace, hyperbolicSum]
    · simp [c, j, flipSpace, Y''.gram_eq, gradedGram, gradedBlocks, hyperbolicSum,
        Matrix.one_apply]
    · simp [c, j, flipSpace, hyperbolicSum]
  · rcases b with (e | e) | b | b | ⟨⟩
    · exact e.elim
    · exact e.elim
    · simp [c, j, flipSpace, Y.gram_eq, gradedGram, gradedBlocks, hyperbolicSum]
    · simp [c, j, flipSpace, hyperbolicSum]
    · have hp_ne : p ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hp; exact Y.N_ne_zero_and_star_eq.1 hp.symm
      have hsp_ne : star p ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hp; exact Y.N_ne_zero_and_star_eq.1 hp.symm
      simp [c, j, flipSpace, Y.gram_eq, gradedGram, gradedBlocks, Fin.rev, hyperbolicSum,
        hs, ← hp]
      field_simp [hp_ne, hsp_ne]

omit [WeilData E] in
private lemma lastDoubleLift_intertwines (hs : s = 1)
    (g : G E (1 : X → ℤˣ)) (k : G E (1 : X₀ → ℤˣ)) :
    let j := (isEmptyElim : Empty ⊕ Empty → ι ⊕ ι'') ⊕ᵥ (Sum.inl ∘ Y.indexEquiv ∘ Sum.inl ⊕ᵥ
      (Sum.inr ∘ Y''.indexEquiv ∘ Sum.inl ⊕ᵥ
        fun _ : Unit ↦ Sum.inl (Y.indexEquiv (Sum.inr ⟨0, hs.ge⟩))))
    let A : Matrix (ι ⊕ ι'') ((Empty ⊕ Empty) ⊕ X ⊕ X₀ ⊕ Unit) E :=
      of fun a b ↦ if a = j b then if b = Sum.inr (Sum.inr (Sum.inr ())) then p⁻¹ else 1 else 0
    fromBlocks (V.ratCoordMatrix (Y.inclX g)) 0 0 (V''.ratCoordMatrix (Y''.inclX k)) *
        A.map toAdele =
      A.map toAdele *
        (G.sum (s := hyperbolicSigns Empty) (1, G.sum (g.neg,
          ((G.blockEmb (e := Equiv.refl (X₀ ⊕ Unit)) Sum.elim_one_one.symm).comp
            (MonoidHom.inl (G E (1 : X₀ → ℤˣ)) (G E (1 : Unit → ℤˣ)))) k))).adeleMatrix := by
  intro j A
  let c : (Empty ⊕ Empty) ⊕ X ⊕ X₀ ⊕ Unit → E :=
    fun b ↦ if b = Sum.inr (Sum.inr (Sum.inr ())) then p⁻¹ else 1
  have h_mul_incl (M : Matrix (ι ⊕ ι'') (ι ⊕ ι'') (𝔸 E)) (a : ι ⊕ ι'')
      (b : (Empty ⊕ Empty) ⊕ X ⊕ X₀ ⊕ Unit) :
      (M * (of fun r c' ↦ if r = j c' then c c' else 0).map toAdele) a b =
        M a (j b) * toAdele (c b) := by
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, apply_ite toAdele,
      map_zero, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have h_rhs :
      (G.sum (s := hyperbolicSigns Empty) (1, G.sum (g.neg,
        ((G.blockEmb (e := Equiv.refl (X₀ ⊕ Unit)) Sum.elim_one_one.symm).comp
          (MonoidHom.inl (G E (1 : X₀ → ℤˣ)) (G E (1 : Unit → ℤˣ)))) k))).adeleMatrix =
        fromBlocks (1 : Matrix (Empty ⊕ Empty) (Empty ⊕ Empty) (𝔸 E)) 0 0
          (fromBlocks g.adeleMatrix 0 0 (fromBlocks k.adeleMatrix 0 0 1)) := by
    simp [G.blockEmb]
  rw [h_rhs]
  refine Matrix.ext fun a b ↦ ?_
  change (fromBlocks (V.ratCoordMatrix (Y.inclX g)) 0 0 (V''.ratCoordMatrix (Y''.inclX k)) *
    (of fun r c' ↦ if r = j c' then c c' else 0).map toAdele) a b = _
  rw [h_mul_incl]
  rcases b with (e | e) | b | b | ⟨⟩
  · exact e.elim
  · exact e.elim
  · rcases a with a | a
    · obtain ⟨u, rfl⟩ := Y.indexEquiv.surjective a
      cases u <;> simp [A, c, j, ratCoordMatrix_inclX, gradedBlocks, Matrix.mul_apply,
        Finset.univ_eq_empty]
    · simp [A, c, j, Matrix.mul_apply, Finset.univ_eq_empty]
  · rcases a with a | a
    · simp [A, c, j, Matrix.mul_apply, Finset.univ_eq_empty]
    · obtain ⟨u, rfl⟩ := Y''.indexEquiv.surjective a
      cases u <;> simp [A, c, j, ratCoordMatrix_inclX, gradedBlocks, Matrix.mul_apply,
        Finset.univ_eq_empty]
  · rcases a with a | a
    · obtain ⟨u, rfl⟩ := Y.indexEquiv.surjective a
      cases u <;> simp [A, c, j, ratCoordMatrix_inclX, gradedBlocks, Matrix.mul_apply,
        Matrix.one_apply, apply_ite toAdele, Finset.univ_eq_empty]
    · simp [A, c, j, Matrix.mul_apply, Finset.univ_eq_empty]

omit [WeilData E] [Fintype X₀] in
private lemma lastDoubleLift_stackedStringMap_apply (h_string : HasConsecutiveStrings Y Y' Y'')
    (hs : s = 1) (a : (Empty ⊕ Empty) ⊕ X ⊕ X₀ ⊕ Unit) (l : ι') :
    let j := (isEmptyElim : Empty ⊕ Empty → ι ⊕ ι'') ⊕ᵥ (Sum.inl ∘ Y.indexEquiv ∘ Sum.inl ⊕ᵥ
      (Sum.inr ∘ Y''.indexEquiv ∘ Sum.inl ⊕ᵥ
        fun _ : Unit ↦ Sum.inl (Y.indexEquiv (Sum.inr ⟨0, hs.ge⟩))))
    let A : Matrix (ι ⊕ ι'') ((Empty ⊕ Empty) ⊕ X ⊕ X₀ ⊕ Unit) E :=
      of fun a b ↦ if a = j b then if b = Sum.inr (Sum.inr (Sum.inr ())) then p⁻¹ else 1 else 0
    stackedStringMap Y Y' Y'' (j a) l =
      ∑ k : Empty, if l = (Function.Embedding.ofIsEmpty (β := {l // Y'.gradeOf l = 1}) k).1 then
        toAdele (A (j a) (Sum.inl (Sum.inr k)) * Y'.genericConst) else 0 := by
  intro j A
  have h_middle : s' = s - 1 := h_string.length_middle
  obtain ⟨u, rfl⟩ := Y'.indexEquiv.surjective l
  rcases u with u | u
  · rcases a with (e | e) | a | a | ⟨⟩
    · exact e.elim
    · exact e.elim
    · simp [j, stackedStringMap, Y.formAdjoint_apply Y', stringMap, gradedBlocks,
        stringReversal, Finset.univ_eq_empty]
    · simp [j, stackedStringMap, stringMap, gradedBlocks, Finset.univ_eq_empty]
    · simp [j, stackedStringMap, Y.formAdjoint_apply Y', stringMap, gradedBlocks,
        stringReversal, Finset.univ_eq_empty]
  · exact absurd u.2 (by omega)

/-- The pair data for s = 1 (so Y' and Y'' have no string), N = pp̄,
`Y'.genericConst = Y.genericConst` and `card ι + card ι''` even: no plane is removed, and z/p, z the
string vector of Y, is adjoined to X₀ as last basis vector of X''. -/
def lastDoubleLift (h_string : HasConsecutiveStrings Y Y' Y'') (h_card : Even (card ι + card ι''))
    (hp : p * star p = N) (hs : s = 1) : DoubleLiftData (X₀ ⊕ Unit) Empty Y Y' Y'' :=
  -- All indices have weight zero here: those of `X`, those of `X₀` and the string vector of `V`.
  let j := isEmptyElim ⊕ᵥ (Sum.inl ∘ Y.indexEquiv ∘ Sum.inl ⊕ᵥ (Sum.inr ∘
    Y''.indexEquiv ∘ Sum.inl ⊕ᵥ fun _ : Unit ↦ Sum.inl (Y.indexEquiv (Sum.inr ⟨0, hs.ge⟩))))
  { zeroPart :=
      { index := ⟨j, by simp [j, Injective]⟩
        mem_range_index incl := by
          exact lastDoubleLift_mem_range_index Y Y' Y'' h_string hs incl
        incl :=
          of fun a b ↦ if a = j b then if b = Sum.inr (Sum.inr (Sum.inr ())) then p⁻¹ else 1 else 0
        incl_eq_zero a b := by
          exact lastDoubleLift_incl_eq_zero Y Y' Y'' h_string hs a b
        -- The string vector has norm `N = p * star p` in `V⁻`; divided by `p` it has norm `1`.
        gram_incl := by exact lastDoubleLift_gram_incl Y Y'' hp hs
        grade_add_eq_zero a b := by exact flipSum_grade_add_eq_zero Y Y'' a b }
    toHasConsecutiveStrings := h_string
    even_card_add := h_card
    -- `k` acts on `X₀` and fixes the last basis vector.
    embX := MonoidHom.comp (G.blockEmb (e := Equiv.refl (X₀ ⊕ Unit)) Sum.elim_one_one.symm)
      (MonoidHom.inl (G E (1 : X₀ → ℤˣ)) (G E (1 : Unit → ℤˣ)))
    det_embX := by simp [G.blockEmb, Subtype.ext_iff]
    intertwines g k := by exact lastDoubleLift_intertwines Y Y'' hs g k
    gradeOne := .ofIsEmpty
    stackedStringMap_apply a l := by
      exact lastDoubleLift_stackedStringMap_apply Y Y' Y'' h_string hs a l }

end EdgePair

end New.Seesaw

/-! ## Gradings of the Y_k and evaluation of consecutive pairs of edges -/

namespace New.Data

open Seesaw WeilData NeZero

variable {P : Parameters} {D : Data P}

/-- The grading of `Y_k` as `X_k` plus a string of length `2 ϱ + 1 - k`, indexed by
`D.indexEquivY k`. As `D.m = 2 ϱ + 2`, the hypothesis says `k < D.m` and the length is
`D.m - 1 - k`. The constant of the generic character, `-(j * (D.M * P.deltaE D.towerExp))⁻¹` with
`j` the purely imaginary element of `New.WeilData`, does not depend on `k`. -/
def gradingY (k : ℕ) (hk : k ≤ 2 * D.ϱ + 1 := by omega) :
    Grading (D.spaceY k) D.N (D.X k) (2 * D.ϱ + 1 - k) where
  indexEquiv := D.indexEquivY k (by grind)
  gram_eq := D.spaceY_gram_eq k (by grind)
  N_ne_zero_and_star_eq := by simp [ne]
  -- `genericConst` is nonzero as `P.deltaE D.towerExp` generates the different, and fixed by
  -- conjugation as `j` and `P.deltaE D.towerExp` are both purely imaginary
  genericConst := ⟨-(j * (D.M * P.deltaE D.towerExp) : D.E)⁻¹, by
               simp [ne, ne_zero_of_differentIdeal_eq_span P.differentIdeal_eq_span_deltaE,
                 ← coe_star_ringOfIntegers, P.star_deltaE, j_ne_zero]⟩

/-- For `M = D.m`, the grading of `Y_M` (whose Gram matrix is `1`) as `D.InitIndex M`, a set of
`n_M - 1` indices in grade 0, plus a string of length 0. -/
def lastGrading {M : ℕ} (e : D.m = M) : Grading (D.spaceY M) D.N (D.InitIndex M) 0 :=
  e ▸ { indexEquiv := (Equiv.sumEmpty (D.InitIndex D.m) (Fin 0)).trans D.lastIndexEquiv.symm
        gram_eq := D.isStd_spaceY_last.std_induction
          (funext₂ (by simp [gradedGram, Matrix.one_apply]))
        N_ne_zero_and_star_eq := by simp [ne]
        genericConst := ⟨1, by simp⟩ }

private lemma doubleLiftEvalY_even_card_middle (D : Data P) {i : ℕ} (_hi : i < D.ϱ) :
    Even (Fintype.card (D.Y (2 * i)) + Fintype.card (D.Y (2 * i + 2))) := by
  simp; grind

private lemma doubleLiftEvalY_even_card_last (D : Data P) {i : ℕ} (hi : D.ϱ = i) :
    Even (Fintype.card (D.Y (2 * i)) + Fintype.card (D.Y (2 * i + 2))) := by
  simp; grind

private lemma doubleLiftEvalY_m_eq (D : Data P) {i : ℕ} (hi : D.ϱ = i) : D.m = 2 * i + 2 := by
  grind

private lemma doubleLiftEvalY_piN_mul_star (D : Data P) :
    (D.piN : D.E) * star (D.piN : D.E) = D.N := by
  exact_mod_cast D.piN_mul_star

/-- The finite evaluation `New.Seesaw.DoubleLiftData.finEval` of the double lift
Y_{2i} → Y_{2i+1} → Y_{2i+2}: for the middle double lift if i < ϱ, the last double lift if i = ϱ,
and 0 beyond. -/
def doubleLiftEvalY (i : ℕ) :=
  if hi : i < D.ϱ then
    (middleDoubleLift (D.gradingY (2 * i) (by omega)) (D.gradingY (2 * i + 1) (by omega))
      (D.gradingY (2 * i + 2) (by omega))
      ⟨⟨D.ϱ - i, by omega⟩, by omega, by omega, rfl⟩
      (by exact doubleLiftEvalY_even_card_middle D hi) (by omega)).finEval
  else if hi : D.ϱ = i then
    -- the last pair, which ends in the space with the trivial grading
    (lastDoubleLift (p := (D.piN : D.E)) (D.gradingY (2 * i) (by omega))
      (D.gradingY (2 * i + 1) (by omega))
      (D.lastGrading (M := 2 * i + 2) (by exact doubleLiftEvalY_m_eq D hi))
      ⟨⟨0, by omega⟩, by omega, by omega, rfl⟩
      (by exact doubleLiftEvalY_even_card_last D hi)
      (by exact doubleLiftEvalY_piN_mul_star D) (by omega)).finEval
  else 0

/-- The natural number `M ^ (f n²)`, with `M = p₀ p₁`, `f` the number of infinite places of `E` and
`n = n_m` the rank `D.n D.m`. -/
abbrev residueMatrixCount : ℕ := D.M ^ (D.f * D.n D.m ^ 2)

/-- For finite adelic points `y k` of the unitary groups, the datum `New.Data.pointDatumY ϑ k` on
Hom(Y_k, Y_{k+1}) moved by `(y k, y (k + 1))` under the finite Weil representation
`New.Seesaw.liftWeilFin` with the character `D.chainChar ϑ (k + 1)` of lift `k + 1`. -/
def translatedPointDatumY (ϑ : D.TameChar) (y : ∀ _ : ℕ, _) (k : ℕ) :=
  liftWeilFin (D.chainChar ϑ (k + 1)) (y k, y (k + 1)) (pointDatumY ϑ k)

/-- The finite evaluation `New.Data.doubleLiftEvalY` of pair i on the data of lifts 2i+1 and 2i+2,
moved by (y_{2i}, y_{2i+1}) and (y_{2i+1}, y_{2i+2}) as in `New.Data.translatedPointDatumY`. -/
def evaluatedDatum (ϑ : D.TameChar) y (i : ℕ) :=
  D.doubleLiftEvalY i
    (arrowProduct (translatedPointDatumY ϑ y (2 * i)).1 (translatedPointDatumY ϑ y (2 * i + 1)).1)

end New.Data

end
