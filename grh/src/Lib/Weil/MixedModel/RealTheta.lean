module

public import Lib.Weil.Construction.ProductsAndTransport
public import Lib.Weil.MixedModel.IsotropicSplitting
public import Lib.Weil.Construction.VacuumProjections

/-!
# Real data, the entire theta function, and the real vacuum in the mixed model

A datum f in `New.𝒮` V is a function on adelic vectors, f(x) = θ(ϱ(x)f), where θ is the theta
functional and ϱ the Heisenberg operators. For v in Fock space we write v ⊗ f = ∫ v(y) ϱ(y) f dy
over real vectors y, and compute its inner products and theta value. If all signs are +1 and f is
fixed by the real vacuum projection, then the theta function Θ_f(y) = f(y) exp(|y|²/2) is entire.
The last part computes the real vacuum and the map `T 0` in a mixed Schrödinger model `T`.

## Main definitions and results

* `New.Space.eq_zero_of_apply_realVec_eq_zero`: f is determined by its values on real vectors, by
  strong approximation and quasi-periodicity under rational vectors.
* `New.Space.entireTheta`: the function Θ_f(y) = f(y) exp(|y|²/2).
* `New.Space.entireTheta_eq_integral`, `New.Space.differentiable_entireTheta`: if all signs are +1
  and inserting the Gaussian as real vector (`New.Space.projReal`) fixes f, then Θ_f is an integral
  against the kernel exp(∑ y_p conj w_p), hence entire.
* `New.Space.Splitting.IsAdapted.omega_projReal_of_isMixedLaw`: in a mixed Schrödinger model `T`,
  the value `T x (ω(g) P f)` is a Gaussian in the real point `x`, for `P` the real vacuum projection
  and `g` adapted to the splitting.
* `New.Space.Splitting.IsAdapted.exists_apply_zero_omega_integrated_eq`: `T 0 ∘ ω(g)` acts on the
  real part by a bounded map of Fock spaces. Here `V.integrated v f`, written v ⊗ f, gives `f` the
  real part `v`, and `V.projReal` is the case of the real vacuum.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.
* `New.realVec`: the additive map from ℂ^{places × n} to 𝔸^n that multiplies the coordinates at τ by
  (2π Im τȷ)^(−1/2) and puts zero at the finite places.
* `New.Fock.realVac`: the function on ℂ^ι sending x to exp(−|x|²/2).
* `New.Space.Splitting.IsMixedLaw`: the law of a mixed Schrödinger model `T x : 𝒮 V → 𝒮 V₀`,
  `x ∈ 𝔸ᵖ`: for `y = l a + ι w + k b`, `T x (ϱ y f)` is `β (2 x + a) b` times `ϱ w (T (x + a) f)`.

## Relation to the literature

Known; see `Lib.Weil.Fock.OscillatorPair` and `Lib.Weil.MixedModel.ZeroTerm` for sources.
-/

@[expose] public section

namespace New.Space

private lemma continuous_sum {α ι M : Type*} [TopologicalSpace α] [AddCommMonoid M]
    [TopologicalSpace M] [ContinuousAdd M] (s : Finset ι) {f : ι → α → M}
    (hf : ∀ i ∈ s, Continuous (f i)) : Continuous fun a ↦ ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using continuous_const
  | insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hf a (Finset.mem_insert_self a s)).fun_add
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-! ## Inner products and theta values of real data -/

section RealData

open Fock Heisenberg Rep

variable {E n : Type*}
  {s : n → ℤˣ} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
  (V : Space E n s) (v w : IsVacuum.Model (realHeisenberg (realSigns E s))) (f f' : 𝒮 V)

/-- For v in the Fock space, f in 𝒮(V) and a bounded linear map T from 𝒮(V) to a Banach space,
T(v ⊗ f) = ∫ v(y) T(ϱ(y) f) dy, with y over real vectors in Fock coordinates (`New.realVec`). -/
lemma map_integrated_eq_integral_realVec {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [CompleteSpace Y] (T : 𝒮 V →L[ℂ] Y) :
    T (V.integrated v f) = ∫ y : NumberField.InfinitePlace E × n → ℂ,
      v y • T (V.ϱ (realVec y) f) ∂normalizedVolume (NumberField.InfinitePlace E × n) := by
  rw [integrated, map_integrated_eq_integral]
  simp_rw [heisenbergRep_left_rho]

/-- For v, w in the Fock space and f, f′ in 𝒮(V), ⟨v ⊗ f, w ⊗ f′⟩ = ⟨v, w⟩ · ⟨Pf, Pf′⟩, where
v ⊗ f = ∫ v(y) ϱ(y) f dy over real vectors y and P is the real vacuum projection. -/
lemma dataInner_integrated :
    V.dataInner (V.integrated v f) (V.integrated w f') =
      fockInner v w * V.dataInner (V.projReal f) (V.projReal f') := by
  -- With the restriction `r` to the finite coordinates, `u ⊗ f` is the product of `u` and `r f`,
  -- and the inner product of two products is the product of the inner products.
  obtain ⟨r, -, hr_integrated⟩ := (adelicSum E s).exists_restriction
  have h_tmul (u : fockSpace (realSigns E s)) (g : 𝒮 V) :
      V.integrated u g = (adelicSum E s).tmul u (r g) :=
    hr_integrated u g
  have h_product (u u' : fockSpace (realSigns E s)) :
      V.dataInner (V.integrated u f) (V.integrated u' f') =
        fockInner u u' * IsVacuum.modelInner (r f) (r f') := by
    rw [h_tmul, h_tmul]
    exact (adelicSum E s).modelInner_tmul u u' (r f) (r f')
  -- `Pf = vac ⊗ f`, and the vacuum is a unit vector.
  have h_vac : fockInner (Fock.vacVector : fockSpace (realSigns E s)) Fock.vacVector = 1 := by
    have h0 := IsVacuum.modelInner_heisenbergOp_vacElem (H := realHeisenberg (realSigns E s))
      (0 : NumberField.InfinitePlace E × n → ℂ) IsVacuum.vacElem
    rw [Rep.rho_zero_apply, IsVacuum.vacElem_apply] at h0
    exact h0.trans (IsVacuum.apply_zero (H := realHeisenberg (realSigns E s)))
  have h_proj : V.dataInner (V.projReal f) (V.projReal f') = IsVacuum.modelInner (r f) (r f') :=
    (h_product Fock.vacVector Fock.vacVector).trans (by rw [h_vac, one_mul])
  rw [h_product, h_proj]

/-- For `v` in the Fock space and `f` in 𝒮(V), `θ(v ⊗ f) = ∫ v(y) f(realVec y) dy`, where
`v ⊗ f = ∫ v(y) ϱ(y)f dy` is `New.Space.integrated` and `f(x) = θ(ϱ(x)f)`. Here `y` runs over
complex vectors indexed by (infinite place, coordinate) with the measure
`New.Fock.normalizedVolume`, and `realVec` turns `y` into an adelic vector by scaling the
coordinates at `τ` by `(2π Im τ(ȷ))^(−1/2)`, with zero at the finite places. -/
lemma theta_integrated :
    V.θ (V.integrated v f) = ∫ y : NumberField.InfinitePlace E × n → ℂ,
      v y * f (realVec y) ∂normalizedVolume (NumberField.InfinitePlace E × n) := by
  rw [map_integrated_eq_integral_realVec]
  simp only [theta_rho, smul_eq_mul]

end RealData

/-!
## The theta function on real vectors

A datum f in `New.𝒮` V is applied to an adelic vector x as f(x) = θ(ϱ(x)f), θ the theta functional
of V. Here this function is restricted to real vectors, `New.realVec` y, with y in complex Fock
coordinates and finite part zero.
-/

section EntireTheta

open MeasureTheory Matrix ComplexConjugate Fock Complex Finset Prod

variable {E : Type _} [Field E] [CMType E] [WeilData E] {n : Type _} [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {V : Space E n s} (f : 𝒮 V)

omit [Fintype n] [DecidableEq n] in
@[fun_prop]
lemma continuous_realVec :
    Continuous (realVec : (NumberField.InfinitePlace E × n → ℂ) → n → 𝔸 E) := by
  refine continuous_pi fun i ↦ Continuous.prodMk ?_ continuous_const
  exact continuous_const.mul (continuous_pi fun w ↦ continuous_apply (w, i))

/-- For f in 𝒮(V), the function Θ_f(y) = θ(ϱ(y)f)·exp(|y|²/2) of a real vector y in Fock
coordinates, placed in the adelic vectors with finite part zero. -/
noncomputable def entireTheta (y : NumberField.InfinitePlace E × n → ℂ) : ℂ :=
  f (realVec y) / realVac y

variable {f}

/-- An element f of 𝒮(V) whose values f(y) = θ(ϱ(y)f) vanish at all adelic vectors y with finite
part zero is zero. -/
lemma eq_zero_of_apply_realVec_eq_zero
    (h_vanish : ∀ y : NumberField.InfinitePlace E × n → ℂ, f (realVec y) = 0) :
    f = 0 := by
  -- By strong approximation the vectors `y` with rational finite part are dense, so it suffices
  -- to show that `f` vanishes at `V.x⁻¹ • y` for these. Translating by a rational vector changes
  -- `f` by a factor only, and removes the finite part.
  let emb : (n → (NumberField.InfinitePlace E → ℂ) × E) → n → 𝔸 E :=
    Pi.map fun _ ↦ Prod.map id (algebraMap E (𝔸f E))
  have h_dense : DenseRange emb :=
    .piMap fun _ ↦ denseRange_id.prodMap denseRange_algebraMap_finAdele
  have h_real (y : n → 𝔸 E) (hy : ∀ i, (y i).2 = 0) : f y = 0 := by
    have hy0 : (fun i : n ↦ ((0 : NumberField.InfinitePlace E → ℂ), (y i).2)) = 0 :=
      funext fun i ↦ Prod.ext rfl (hy i)
    rw [← realVec_realCoord_add y, hy0, add_zero]
    exact h_vanish (realCoord y)
  -- At `V.x⁻¹ • emb a`, adding the vector of the rational `-(a i).2` removes the finite part.
  have h_on_range (a : n → (NumberField.InfinitePlace E → ℂ) × E) :
      f (V.x⁻¹.val *ᵥ emb a) = 0 := by
    have h_finite (i : n) : ((V.vecAtPoint (-snd ∘ a) + V.x⁻¹.val *ᵥ emb a) i).2 = 0 := by
      change ((V.x⁻¹.val *ᵥ (toAdele ∘ (-snd ∘ a)) + V.x⁻¹.val *ᵥ emb a) i).2 = 0
      rw [← mulVec_add, mulVec, dotProduct, snd_sum]
      refine sum_eq_zero fun j _ ↦ ?_
      rw [snd_mul, Pi.add_apply, snd_add]
      change (V.x⁻¹.val i j).2 *
        (algebraMap E (𝔸f E) (-(a j).2) + algebraMap E (𝔸f E) (a j).2) = 0
      rw [(algebraMap E (𝔸f E)).map_neg, neg_add_cancel, mul_zero]
    rw [← V.apply_vecAtPoint_add f (-snd ∘ a), h_real _ h_finite, mul_zero]
  have hf_cont : Continuous fun z : n → 𝔸 E ↦ f (V.x⁻¹ • z) :=
    V.rawTheta.cont.comp
      (V.heisenbergRep.cont.comp ((continuous_const_smul V.x⁻¹).prodMk continuous_const))
  have h_translate (z : n → 𝔸 E) : f (V.x⁻¹ • z) = 0 :=
    congrFun (h_dense.equalizer hf_cont continuous_const (funext h_on_range)) z
  refine V.data_ext fun x ↦ ?_
  obtain ⟨z, rfl⟩ := MulAction.surjective V.x⁻¹ x
  rw [Space.zero_apply]
  exact h_translate z

/-- If all signs are +1 and inserting the Gaussian as real vector fixes f, then
Θ_f(y) = ∫ exp(∑_p y_p conj w_p) exp(−|w|²/2) f(w) dw, over real vectors w with Lebesgue
measure divided by π to the number of coordinates. -/
lemma entireTheta_eq_integral (hs : s = 1) (h_projReal : V.projReal f = f)
    (y : NumberField.InfinitePlace E × n → ℂ) :
    entireTheta f y = ∫ w : NumberField.InfinitePlace E × n → ℂ,
      Complex.exp (∑ p : NumberField.InfinitePlace E × n, y p * conj (w p)) *
        (realVac w * f (realVec w)) ∂normalizedVolume (NumberField.InfinitePlace E × n) := by
  -- As `f` is `V.integrated vacVector f`, its value at `realVec y` is an integral against the
  -- translated vacuum.
  have h_value : f (realVec y) = ∫ w, realHeisenbergOp y (Fock.vacVector (ε := realSigns E s)) w *
      f (realVec w) ∂normalizedVolume _ := by
    rw [← theta_integrated, integrated_realHeisenbergOp, h_projReal, theta_rho]
  -- By `beta_mul_realVac` the translated vacuum at `w` is `realVac w * realVac y` times the
  -- exponential.
  have h_hol (x : NumberField.InfinitePlace E × n → ℂ) :
      holomorphicCoord (realSigns E s) x = star x := by
    rw [holomorphicCoord_eq]
    funext p
    simp only [realSigns, hs, Pi.one_apply, ↓reduceIte, Pi.star_apply]
  have h_translate (w : NumberField.InfinitePlace E × n → ℂ) :
      realHeisenbergOp y (Fock.vacVector (ε := realSigns E s)) w =
        realVac w * realVac y * exp (∑ p, y p * conj (w p)) := by
    rw [Heisenberg.IsVacuum.heisenbergOp_apply (H := realHeisenberg (realSigns E s)),
      Heisenberg.IsVacuum.vacElem_apply (H := realHeisenberg (realSigns E s)),
      beta_mul_realVac, h_hol, h_hol, star_star]
    rfl
  have h_ne : realVac y ≠ 0 := exp_ne_zero _
  rw [entireTheta, h_value, ← integral_div]
  congr 1
  funext w
  rw [h_translate w, show realVac w * realVac y * exp (∑ p, y p * conj (w p)) * f (realVec w) =
      realVac y * (exp (∑ p, y p * conj (w p)) * (realVac w * f (realVec w))) by ring,
    mul_div_cancel_left₀ _ h_ne]

/-- Suppose all signs `s` are +1 and `f` is fixed by the real vacuum projection
`f ↦ ∫ exp(−|y|²/2) ϱ(y)f dy` (`projReal`). Then `Θ_f(y) = θ(ϱ(y)f)·exp(|y|²/2)` is complex
differentiable everywhere as a function of the complex vector `y`, indexed by (infinite place,
coordinate), that gives a real vector in Fock coordinates. -/
@[fun_prop]
lemma differentiable_entireTheta (hs : s = 1) (h_projReal : V.projReal f = f) :
    Differentiable ℂ (entireTheta f) := by
  -- Differentiate the integral formula `entireTheta_eq_integral` under the integral sign.
  rw [funext (entireTheta_eq_integral hs h_projReal)]
  have h_vac_f : Continuous fun w : NumberField.InfinitePlace E × n → ℂ ↦
      realVac w * f (realVec w) :=
    (Heisenberg.IsVacuum.cont (H := realHeisenberg (realSigns E s))).mul
      (V.rawTheta.cont.comp
        (V.heisenbergRep.cont.comp (continuous_realVec.prodMk continuous_const)))
  have h_meas (z : NumberField.InfinitePlace E × n → ℂ) :
      AEStronglyMeasurable
        (fun w ↦ (∑ p, z p * conj (w p)).exp * (realVac w * f (realVec w)))
        (normalizedVolume _) :=
    (((continuous_sum univ fun p _ ↦
        continuous_const.mul (Complex.continuous_conj.comp (continuous_apply p))).cexp).mul
      h_vac_f).aestronglyMeasurable
  intro y
  -- For `‖z‖ < ‖y‖ + 1` the integrand is dominated by one integrable function of `w`.
  let C : ℝ := ∑ _p : NumberField.InfinitePlace E × n, (‖y‖ + 1)
  have h_dominated : ∀ᶠ z in nhds y, ∀ w : NumberField.InfinitePlace E × n → ℂ,
      DifferentiableAt ℂ (fun z' ↦ (∑ p, z' p * conj (w p)).exp * (realVac w * f (realVec w))) z ∧
        ‖(∑ p, z p * conj (w p)).exp * (realVac w * f (realVec w))‖ ≤
          (C * ‖w‖).exp * ‖realVac w‖ * (‖V.θ‖ * ‖f‖) := by
    filter_upwards [tendsto_norm.eventually_lt_const (lt_add_one ‖y‖)] with z hz w
    refine ⟨((DifferentiableAt.fun_sum fun p _ ↦
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : NumberField.InfinitePlace E × n ↦ ℂ)
          p).differentiableAt.mul_const (conj (w p))).cexp).mul_const _, ?_⟩
    have h_exponent : ‖∑ p, z p * conj (w p)‖ ≤ C * ‖w‖ := by
      refine (norm_sum_le_of_le _ fun p _ ↦ ?_).trans_eq (sum_mul univ (fun _ ↦ ‖y‖ + 1) ‖w‖).symm
      rw [norm_mul, norm_conj]
      exact mul_le_mul ((norm_le_pi_norm z p).trans hz.le) (norm_le_pi_norm w p) (norm_nonneg _)
        ((norm_nonneg z).trans hz.le)
    rw [norm_mul, norm_mul, ← mul_assoc]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right
        ((norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr h_exponent)) (norm_nonneg _))
      (V.norm_apply_le (realVec w) f) (norm_nonneg _)
      (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))
  exact (eventually_differentiableAt_integral ((integrable_exp_mul_realVac C).mul_const _)
    h_meas h_dominated).self_of_nhds

end EntireTheta

end New.Space

/-!
## The real vacuum in a mixed Schrödinger model

A splitting `D` (`New.Space.Splitting`) writes `V` as `l Eᵖ ⊕ ι V₀ ⊕ k Eᵖ` with `l`, `k` isotropic
and dual. Only the infinite places are treated. The last three results concern an element `g` of
`G E s` adapted to some `t` in `GL_p(𝔸)` (`New.Space.Splitting.IsAdapted`): the matrix
`g⁻¹ (l (t⁻¹)ᴴ, k t, ι)` has orthonormal columns at the infinite places and integral finite entries.
-/

namespace New.Space.Splitting

open NumberField Matrix Fock Exchange Prod Complex Fintype ComplexOrder MeasureTheory Heisenberg Rep
  IsVacuum

variable {E : Type _} [Field E] [CMType E] [WeilData E] {n n₀ p : Type _} [Fintype n]
  [DecidableEq n] [Fintype n₀] [DecidableEq n₀] [Fintype p] [DecidableEq p] {s : n → ℤˣ}
  {s₀ : n₀ → ℤˣ} {V : Space E n s} {V₀ : Space E n₀ s₀} {D : V.Splitting V₀ p}
  (L : 𝒮 V →L[ℂ] 𝒮 V₀) (A : Matrix n p (𝔸 E)) {T : (p → 𝔸 E) → 𝒮 V →L[ℂ] 𝒮 V₀}

/-- The archimedean part of an adelic matrix A as one complex matrix, block diagonal over the
infinite places, whose block at τ is the τ-component of A. -/
noncomputable def realMatrix {E : Type _} [Field E] [NumberField E] (A : Matrix n p (𝔸 E)) :
    Matrix (InfinitePlace E × n) (InfinitePlace E × p) ℂ :=
  (blockDiagonal (A.map <| evalInf ·)).submatrix Prod.swap Prod.swap

/-- In the coordinates of the orthogonal sum of `s` and `s₀` (`New.Fock.realCoordSum`, whose `equiv`
joins a pair into one function on places × (n ⊕ n₀); `⊕ᵥ` joins two vectors likewise), `realVec` of
a pair is the pair of the `realVec`s. -/
lemma realVec_realCoordSum (x : (InfinitePlace E × n → ℂ) × (InfinitePlace E × n₀ → ℂ)) :
    realVec
        ((realCoordSum (realSigns_comp_split (E := E) (signs_comp_refl (t := s ⊕ᵥ s₀)))).equiv x) =
      realVec x.fst ⊕ᵥ realVec x.snd := by
  simp only [realCoordSum]
  funext i
  rcases i with i | i <;> rfl

omit [Fintype n] [DecidableEq n] [DecidableEq p] in
/-- Acting by `realMatrix A` in Fock's coordinates is acting by `A` on real adelic vectors. -/
lemma realVec_realMatrix_mulVec (y : InfinitePlace E × p → ℂ) :
    realVec (realMatrix A *ᵥ y) = A *ᵥ realVec y := by
  funext i
  refine Prod.ext (funext fun w ↦ ?_) ?_
  · change (WeilData.scaleIdele E).1.1 w * (realMatrix A *ᵥ y) (w, i) = ((A *ᵥ realVec y) i).1 w
    rw [mulVec, dotProduct, sum_prod_type_right, Finset.mul_sum,
      mulVec, dotProduct, fst_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have h_inner :
        ∑ w' : InfinitePlace E, realMatrix A (w, i) (w', j) * y (w', j) =
          (A i j).1 w * y (w, j) := by
      simp only [realMatrix, submatrix_apply, Prod.swap_prod_mk, blockDiagonal_apply,
        Matrix.map_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      rfl
    rw [h_inner]
    exact mul_left_comm ((WeilData.scaleIdele E).1.1 w) ((A i j).1 w) (y (w, j))
  · change (0 : 𝔸f E) = ((A *ᵥ realVec y) i).2
    rw [mulVec, dotProduct, snd_sum]
    exact (Finset.sum_eq_zero fun j _ ↦ mul_zero ((A i j).2)).symm

omit [WeilData E] [DecidableEq n] [Fintype p] in
/-- If `A` has orthonormal columns at the infinite places (and integral finite entries), then
`realMatrix A` has orthonormal columns. -/
lemma conjTranspose_realMatrix_mul_self (hA : IsOrthoIntegral A) :
    (realMatrix A)ᴴ * realMatrix A = 1 := by
  -- `realMatrix A` reorders a block diagonal matrix; by `h_orth` each block, the component of
  -- `A` at an infinite place, has orthonormal columns.
  obtain ⟨h_orth, -⟩ := hA
  rw [realMatrix, conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Prod.swap_bijective,
    blockDiagonal_conjTranspose, ← blockDiagonal_mul,
    show (fun w ↦ (A.map (evalInf w))ᴴ * A.map (evalInf w)) = 1 from funext h_orth,
    blockDiagonal_one, submatrix_one _ Prod.swap_injective]

/-- For a splitting of V over V₀, write y = la + ιw + kb and y' = la' + ιw' + kb'. Then
β(y,y') = ψ(½ȷ(a'*b + b'*a)) β₀(w,w'), with β₀ the bicharacter for the signs of V₀. -/
lemma beta_eq_coords (y y' : n → 𝔸 E) :
    (adelicHeisenberg E s).β y y' =
      (adelicHeisenberg E 1).β (D.kCoord *ᵥ y) (D.lCoord *ᵥ y') *
        (adelicHeisenberg E 1).β (D.lCoord *ᵥ y) (D.kCoord *ᵥ y') *
        (adelicHeisenberg E s₀).β (D.iCoord *ᵥ y) (D.iCoord *ᵥ y') := by
  -- Split `y` along `k`, `ι`, `l` and pair each part with `y'`.
  have h_k : star (D.lCoord *ᵥ y') ⬝ᵥ stdForm E 1 *ᵥ (D.kCoord *ᵥ y) =
      star y' ⬝ᵥ stdForm E s *ᵥ ((D.kAdelic * D.kCoord) *ᵥ y) := by
    rw [stdForm_one, one_mulVec, star_mulVec_dotProduct, D.conjTranspose_lCoord,
      mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have h_l : star (D.kCoord *ᵥ y') ⬝ᵥ stdForm E 1 *ᵥ (D.lCoord *ᵥ y) =
      star y' ⬝ᵥ stdForm E s *ᵥ ((D.lAdelic * D.lCoord) *ᵥ y) := by
    rw [stdForm_one, one_mulVec, star_mulVec_dotProduct, D.conjTranspose_kCoord,
      mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have h_i : star (D.iCoord *ᵥ y') ⬝ᵥ stdForm E s₀ *ᵥ (D.iCoord *ᵥ y) =
      star y' ⬝ᵥ stdForm E s *ᵥ ((D.iAdelic * D.iCoord) *ᵥ y) := by
    rw [star_mulVec_dotProduct, mulVec_mulVec, D.conjTranspose_iCoord, Matrix.mul_assoc,
      Matrix.mul_assoc, stdForm_mul_self, Matrix.mul_one, mulVec_mulVec, mulVec_mulVec,
      Matrix.mul_assoc]
  have h_dot : star y' ⬝ᵥ stdForm E s *ᵥ y =
      star (D.lCoord *ᵥ y') ⬝ᵥ stdForm E 1 *ᵥ (D.kCoord *ᵥ y) +
      star (D.kCoord *ᵥ y') ⬝ᵥ stdForm E 1 *ᵥ (D.lCoord *ᵥ y) +
      star (D.iCoord *ᵥ y') ⬝ᵥ stdForm E s₀ *ᵥ (D.iCoord *ᵥ y) := by
    rw [h_k, h_l, h_i, ← dotProduct_add, ← dotProduct_add, ← mulVec_add, ← mulVec_add,
      ← add_mulVec, ← add_mulVec, add_right_comm, D.sum_frame_mul_coord_eq_one, one_mulVec]
  simp only [adelicHeisenberg, h_dot, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul]

/-- If a bounded map `L : 𝒮 V → 𝒮 V₀` is (a) invariant under the Heisenberg operators along `k`
and (b) intertwines those of `V₀`, then the family `x ↦ L ϱ(l x)` obeys the law of a mixed
model. -/
lemma isMixedLaw_comp_rho
    (hk : ∀ (b : p → 𝔸 E) (f : 𝒮 V), L (V.ϱ (D.kAdelic *ᵥ b) f) = L f)
    (hi : ∀ (w : n₀ → 𝔸 E) (f : 𝒮 V), L (V.ϱ (D.iAdelic *ᵥ w) f) = V₀.ϱ w (L f)) :
    D.IsMixedLaw fun x : p → 𝔸 E ↦ L ∘L V.ϱ (D.lAdelic *ᵥ x) := by
  intro x y f
  -- Split y = k b + ι w + l a. By `hk` the left side may be preceded by ϱ(-k b), and by `hi` the
  -- operator ϱ(w) on the right moves inside L as ϱ(ι w).
  set b : p → 𝔸 E := D.kCoord *ᵥ y
  set w : n₀ → 𝔸 E := D.iCoord *ᵥ y
  set a : p → 𝔸 E := D.lCoord *ᵥ y
  have h_split : y = D.kAdelic *ᵥ b + D.iAdelic *ᵥ w + D.lAdelic *ᵥ a := by
    simp only [b, w, a, mulVec_mulVec, ← add_mulVec, D.sum_frame_mul_coord_eq_one, one_mulVec]
  have h_beta_l (u : p → 𝔸 E) :
      (adelicHeisenberg E s).β (D.lAdelic *ᵥ u) y = (adelicHeisenberg E 1).β u b := by
    rw [D.beta_eq_coords]
    simp only [mulVec_mulVec, D.coord_mul_frame, one_mulVec, zero_mulVec,
      beta_zero_left, one_mul, mul_one, b]
  have h_beta_k (u : p → 𝔸 E) (v : n → 𝔸 E) :
      (adelicHeisenberg E s).β (D.kAdelic *ᵥ u) v =
        (adelicHeisenberg E 1).β u (D.lCoord *ᵥ v) := by
    rw [D.beta_eq_coords]
    simp only [mulVec_mulVec, D.coord_mul_frame, one_mulVec, zero_mulVec,
      beta_zero_left, mul_one]
  have h_beta_i (u : n₀ → 𝔸 E) (v : p → 𝔸 E) :
      (adelicHeisenberg E s).β (D.iAdelic *ᵥ u) (D.lAdelic *ᵥ v) = 1 := by
    rw [D.beta_eq_coords]
    simp only [mulVec_mulVec, D.coord_mul_frame, one_mulVec, zero_mulVec,
      beta_zero_left, beta_zero_right, mul_one]
  have h_vec :
      D.kAdelic *ᵥ (-b) + D.lAdelic *ᵥ x + y = D.iAdelic *ᵥ w + D.lAdelic *ᵥ (x + a) := by
    rw [h_split, mulVec_neg, mulVec_add]
    abel
  simp only [ContinuousLinearMap.comp_apply]
  rw [← hk (-b), ← hi w, V.heisenbergRep.mul, V.heisenbergRep.mul, V.heisenbergRep.mul,
    L.map_smul, L.map_smul, L.map_smul, h_beta_k, mulVec_mulVec, D.lCoord_mul_lAdelic, one_mulVec,
    add_left, h_beta_k, h_beta_l, beta_neg_left, beta_neg_left, h_beta_i, one_smul, h_vec,
    smul_smul, ← add_left, add_comm a x, ← add_left]

/-- The Gaussian integral along the isotropic frame `k`. With e(y) = exp(−|y|²/2) and β the
bicharacter of `realHeisenberg 1` on ℂ^ι, the integral of β(2x + c, b) e(c) e(b) over b is
exp(−|x|²) e(x + c)² 2^|ι|. -/
lemma integral_beta_mul_realVac {ι : Type*} [Fintype ι] [DecidableEq ι] (x c : ι → ℂ) :
    ∫ b : ι → ℂ, (realHeisenberg 1).β (x + (x + c)) b * (realVac c * realVac b) ∂normalizedVolume ι
      = exp (-(star x ⬝ᵥ x)) * (realVac (x + c) ^ 2 * 2 ^ Fintype.card ι) := by
  set y : ι → ℂ := x + (x + c) with hy
  -- The integral of exp(-(b + y)*(b - y) / 2) over b, by a shift in `integral_gauss`.
  have h_gauss :
      ∫ b : ι → ℂ, exp (-(2⁻¹ * (star b ⬝ᵥ b + star y ⬝ᵥ b - (star b ⬝ᵥ y + star y ⬝ᵥ y))))
        ∂normalizedVolume ι = 2 ^ Fintype.card ι := by
    simpa using (integral_add_right_eq_self _ y).trans
      (integral_gauss (A := scalar ι 2⁻¹) (by simp [IsAccretive, add_pos]) (y + y))
  have h_square (b : ι → ℂ) :
      (realHeisenberg 1).β y b * (realVac c * realVac b) = realVac c * realVac y *
        exp (-(2⁻¹ * (star b ⬝ᵥ b + star y ⬝ᵥ b - (star b ⬝ᵥ y + star y ⬝ᵥ y)))) := by
    have h_β : (realHeisenberg 1).β y b = exp ((star b ⬝ᵥ y - star y ⬝ᵥ b) / 2) := by
      simp only [realHeisenberg, signMatrix, Pi.one_apply, Units.val_one, Int.cast_one,
        diagonal_one, one_mulVec]
    simp only [h_β, realVac, ← exp_add]
    congr 1
    ring
  -- The parallelogram identity |c|² + |2x + c|² = 2|x|² + 2|x + c|².
  have h_parallelogram : realVac c * realVac y = exp (-(star x ⬝ᵥ x)) * realVac (x + c) ^ 2 := by
    simp only [hy, realVac, sq, ← exp_add, star_add, add_dotProduct, dotProduct_add]
    congr 1
    ring
  simp_rw [h_square, integral_const_mul, h_gauss, h_parallelogram, mul_assoc]

/-- The real vacuum is a Gaussian in the mixed model. Let `T` obey the law of a mixed model
(`IsMixedLaw`) for the splitting `D`, and let `g` be adapted to `t` (`IsAdapted`). With `P`, `P₀`
the real vacuum projections of `V`, `V₀`, we have
`T x (ω(g) P f) = exp(−|a|²) P₀ (T 0 (ω(g) P f))` at the point `x = (t⁻¹)ᴴ (realVec a)`. -/
lemma IsAdapted.omega_projReal_of_isMixedLaw (hT : D.IsMixedLaw T) {g : G E s}
    {t : GL p (𝔸 E)} (hg : D.IsAdapted g t) (a : InfinitePlace E × p → ℂ) (f : 𝒮 V) :
    T (t.val⁻¹ᴴ *ᵥ realVec a) (V.ω g (V.projReal f)) =
      exp (-(Star.star a ⬝ᵥ a)) • V₀.projReal (T 0 (V.ω g (V.projReal f))) := by
  -- Write P f = ∫ e(y) ϱ(y) f dy, e the Gaussian, in the coordinates y = (c, b, w) of the adapted
  -- frame. Under T the b-integral is a Gaussian integral and the w-integral is P₀. This gives
  -- T((t⁻¹)ᴴ realVec x) ω(g) P f = exp(-|x|²) C with C independent of x; compare with x = 0.
  have h_orth : (realMatrix (D.frameAt g t))ᴴ * realMatrix (D.frameAt g t) = 1 :=
    conjTranspose_realMatrix_mul_self _ hg
  have h_card : card (InfinitePlace E × ((p ⊕ p) ⊕ n₀)) = card (InfinitePlace E × n) := by
    simp only [card_prod, card_sum, D.card_eq]
    ring
  have h_orth' : realMatrix (D.frameAt g t) * (realMatrix (D.frameAt g t))ᴴ = 1 :=
    (mul_eq_one_comm_of_card_eq _ _ _ h_card).1 h_orth
  -- The frame is a unitary matrix, so it keeps the Gaussian and hence (`measurePreserving_equiv`)
  -- the measure.
  have h_vac (y : InfinitePlace E × ((p ⊕ p) ⊕ n₀) → ℂ) :
      realVac (realMatrix (D.frameAt g t) *ᵥ y) = realVac y := by
    rw [realVac, realVac, star_mulVec_dotProduct, mulVec_mulVec, h_orth, one_mulVec]
  let φ : (InfinitePlace E × ((p ⊕ p) ⊕ n₀) → ℂ) ≃ₜ+ (InfinitePlace E × n → ℂ) :=
    { toFun := (realMatrix (D.frameAt g t) *ᵥ ·)
      invFun := ((realMatrix (D.frameAt g t))ᴴ *ᵥ ·)
      left_inv y := by dsimp only; rw [mulVec_mulVec, h_orth, one_mulVec]
      right_inv y := by dsimp only; rw [mulVec_mulVec, h_orth', one_mulVec]
      map_add' := mulVec_add _
      continuous_toFun := continuous_pi fun i ↦ continuous_sum Finset.univ fun j _ ↦
        continuous_const.mul (continuous_apply j)
      continuous_invFun := continuous_pi fun i ↦ continuous_sum Finset.univ fun j _ ↦
        continuous_const.mul (continuous_apply j) }
  have h_frame : MeasurePreserving (realMatrix (D.frameAt g t) *ᵥ ·) (normalizedVolume _)
      (normalizedVolume _) :=
    measurePreserving_equiv (realHeisenberg 1) (realHeisenberg 1) (φ := φ) h_vac
  -- Splitting the coordinates as ((c, b), w), and then as (c, b), preserves the measure too.
  let outer : (realHeisenberg (realSigns E ((1 : p ⊕ p → ℤˣ) ⊕ᵥ s₀))).OrthogonalSum
      (realHeisenberg (realSigns E (1 : p ⊕ p → ℤˣ))) (realHeisenberg (realSigns E s₀)) realVac :=
    realCoordSum (realSigns_comp_split signs_comp_refl)
  let inner : (realHeisenberg (realSigns E ((1 : p → ℤˣ) ⊕ᵥ (1 : p → ℤˣ)))).OrthogonalSum
      (realHeisenberg (realSigns E (1 : p → ℤˣ))) (realHeisenberg (realSigns E (1 : p → ℤˣ)))
        realVac :=
    realCoordSum (realSigns_comp_split signs_comp_refl)
  let coord (c b : InfinitePlace E × p → ℂ) (w : InfinitePlace E × n₀ → ℂ) :
      InfinitePlace E × n → ℂ :=
    realMatrix (D.frameAt g t) *ᵥ outer.equiv (inner.equiv (c, b), w)
  have h_fubini (F : (InfinitePlace E × n → ℂ) → 𝒮 V₀) (hF : Integrable F (normalizedVolume _)) :
      ∫ y, F y ∂normalizedVolume _ =
        ∫ c, ∫ b, ∫ w, F (coord c b w) ∂normalizedVolume _ ∂normalizedVolume _ ∂normalizedVolume
          _ := by
    obtain ⟨h_int, h_outer⟩ := (h_frame.comp outer.measurePreserving_equiv).fubini hF
    exact h_outer.symm.trans
      (inner.measurePreserving_equiv.integral_integral_comp h_int.integral_prod_left).symm
  -- The character of the law at real vectors is the real bicharacter.
  have h_char (y b : InfinitePlace E × p → ℂ) :
      (adelicHeisenberg E 1).β (realVec y) (realVec b) = (realHeisenberg 1).β y b := by
    have h := (adelicSum E (n := p) 1).beta_equiv (y, 0) (b, 0)
    rw [adelicSum_real_eq_realVec, adelicSum_real_eq_realVec, beta_zero_left, mul_one] at h
    exact h
  let N (x : InfinitePlace E × p → ℂ) : 𝒮 V →L[ℂ] 𝒮 V₀ := T (t.val⁻¹ᴴ *ᵥ realVec x) ∘L V.ω g
  -- The law of T in the coordinates (c, b, w).
  have h_law (x c b : InfinitePlace E × p → ℂ) (w : InfinitePlace E × n₀ → ℂ) :
      N x (V.ϱ (realVec (coord c b w)) f) =
        (realHeisenberg 1).β (x + (x + c)) b • V₀.ϱ (realVec w) (N (x + c) f) := by
    have h_vec : realVec (outer.equiv (inner.equiv (c, b), w)) =
        (realVec c ⊕ᵥ realVec b) ⊕ᵥ realVec w := by
      simp only [outer, inner, realVec_realCoordSum]
    have h_g_coord : g.adeleMatrix *ᵥ realVec (coord c b w) =
        D.lAdelic *ᵥ (t.val⁻¹ᴴ *ᵥ realVec c) + D.kAdelic *ᵥ (t.val *ᵥ realVec b) +
          D.iAdelic *ᵥ realVec w := by
      dsimp only [coord]
      rw [realVec_realMatrix_mulVec, h_vec, mulVec_mulVec, frameAt, ← Matrix.mul_assoc,
        ← G.adeleMatrix_mul, mul_inv_cancel, G.adeleMatrix_one, Matrix.one_mul,
        fromCols_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
        fromCols_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
        ← mulVec_mulVec, ← mulVec_mulVec, coe_units_inv]
    have h_l : D.lCoord *ᵥ (g.adeleMatrix *ᵥ realVec (coord c b w)) = t.val⁻¹ᴴ *ᵥ realVec c := by
      rw [h_g_coord, mulVec_add, mulVec_add, mulVec_mulVec _ D.lCoord D.lAdelic,
        D.lCoord_mul_lAdelic, one_mulVec, mulVec_mulVec _ D.lCoord D.kAdelic, D.lCoord_mul_kAdelic,
        zero_mulVec, mulVec_mulVec _ D.lCoord D.iAdelic, D.lCoord_mul_iAdelic, zero_mulVec,
        add_zero, add_zero]
    have h_k : D.kCoord *ᵥ (g.adeleMatrix *ᵥ realVec (coord c b w)) = t.val *ᵥ realVec b := by
      rw [h_g_coord, mulVec_add, mulVec_add, mulVec_mulVec _ D.kCoord D.lAdelic,
        D.kCoord_mul_lAdelic, zero_mulVec, mulVec_mulVec _ D.kCoord D.kAdelic, D.kCoord_mul_kAdelic,
        one_mulVec, mulVec_mulVec _ D.kCoord D.iAdelic, D.kCoord_mul_iAdelic, zero_mulVec,
        zero_add, add_zero]
    have h_i : D.iCoord *ᵥ (g.adeleMatrix *ᵥ realVec (coord c b w)) = realVec w := by
      rw [h_g_coord, mulVec_add, mulVec_add, mulVec_mulVec _ D.iCoord D.lAdelic,
        D.iCoord_mul_lAdelic, zero_mulVec, mulVec_mulVec _ D.iCoord D.kAdelic, D.iCoord_mul_kAdelic,
        zero_mulVec, mulVec_mulVec _ D.iCoord D.iAdelic, D.iCoord_mul_iAdelic, one_mulVec,
        zero_add, zero_add]
    have h_sum : t.val⁻¹ᴴ *ᵥ realVec x + t.val⁻¹ᴴ *ᵥ realVec c = t.val⁻¹ᴴ *ᵥ realVec (x + c) := by
      rw [← mulVec_add, ← realVec.map_add]
    have h_beta :
        (adelicHeisenberg E 1).β (t.val⁻¹ᴴ *ᵥ realVec x + t.val⁻¹ᴴ *ᵥ realVec (x + c))
          (t.val *ᵥ realVec b) = (adelicHeisenberg E 1).β (realVec (x + (x + c))) (realVec b) := by
      rw [← mulVec_add, ← realVec.map_add]
      dsimp only [adelicHeisenberg]
      congr 2
      rw [stdForm_one, one_mulVec, one_mulVec, star_mulVec_dotProduct, mulVec_mulVec,
        ← conjTranspose_mul, ← coe_units_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        conjTranspose_one, one_mulVec]
    dsimp only [N]
    rw [ContinuousLinearMap.comp_apply, omega_rho, hT, h_l, h_k, h_i, h_sum, h_beta, h_char]
    rfl
  have h_vac_coord (c b : InfinitePlace E × p → ℂ) (w : InfinitePlace E × n₀ → ℂ) :
      realVac (coord c b w) = realVac c * realVac b * realVac w := by
    simp only [coord, h_vac, OrthogonalSum.vac_equiv]
  -- The main formula, after any bounded operator M.
  have key (x : InfinitePlace E × p → ℂ) (M : 𝒮 V₀ →L[ℂ] 𝒮 V₀) :
      M (N x (V.projReal f)) = exp (-(star x ⬝ᵥ x)) •
        ∫ c, (realVac c ^ 2 * 2 ^ Fintype.card (InfinitePlace E × p)) •
          M (V₀.projReal (N c f)) ∂normalizedVolume _ := by
    have h_int : Integrable (fun y ↦ realVac y • M (N x (V.ϱ (realVec y) f)))
        (normalizedVolume _) :=
      (Fock.vacVector (ε := realSigns E s)).integrable.smul_bdd (‖M ∘L N x‖ * ‖f‖)
        ((M ∘L N x).continuous.comp
          (V.heisenbergRep.cont.comp
            (continuous_realVec.prodMk continuous_const))).aestronglyMeasurable
        (.of_forall fun y ↦
          ((M ∘L N x).le_opNorm (V.ϱ (realVec y) f)).trans_eq (by rw [Rep.norm_map]))
    -- The w-integral is the projection on the real vacuum of `V₀`.
    have h_proj (u : 𝒮 V₀) :
        ∫ w, realVac w • M (V₀.ϱ (realVec w) u) ∂normalizedVolume _ = M (V₀.projReal u) :=
      (V₀.map_integrated_eq_integral_realVec Fock.vacVector u M).symm
    have h_step (c : InfinitePlace E × p → ℂ) :
        (∫ b, ∫ w, realVac (coord c b w) • M (N x (V.ϱ (realVec (coord c b w)) f))
          ∂normalizedVolume _ ∂normalizedVolume _) =
        exp (-(star x ⬝ᵥ x)) •
          (realVac (x + c) ^ 2 * 2 ^ Fintype.card (InfinitePlace E × p)) •
            M (V₀.projReal (N (x + c) f)) := by
      have h_inner (b : InfinitePlace E × p → ℂ) :
          (∫ w, realVac (coord c b w) • M (N x (V.ϱ (realVec (coord c b w)) f))
            ∂normalizedVolume _) =
          ((realHeisenberg 1).β (x + (x + c)) b * (realVac c * realVac b)) •
            M (V₀.projReal (N (x + c) f)) := by
        rw [← h_proj (N (x + c) f), ← integral_smul]
        congr 1; funext w
        rw [h_law, h_vac_coord, M.map_smul, smul_smul, smul_smul]
        congr 1
        ring
      simp_rw [h_inner]
      rw [integral_smul_const, integral_beta_mul_realVac, mul_smul]
    rw [show M (N x (V.projReal f)) =
        ∫ y, realVac y • M (N x (V.ϱ (realVec y) f)) ∂normalizedVolume _ from
      V.map_integrated_eq_integral_realVec Fock.vacVector f (M ∘L N x), h_fubini _ h_int]
    simp_rw [h_step]
    rw [integral_smul]
    exact congrArg _ (integral_add_left_eq_self (fun c ↦
      (realVac c ^ 2 * 2 ^ Fintype.card (InfinitePlace E × p)) • M (V₀.projReal (N c f))) x)
  -- At x = 0 the formula with M = P₀ identifies the integral with P₀ T₀ ω(g) P f.
  have h_proj_idem (u : 𝒮 V₀) : V₀.projReal (V₀.projReal u) = V₀.projReal u := by
    rw [projReal, integrated_integrated,
      IsVacuum.vacElem_apply (H := realHeisenberg (realSigns E s₀)),
      IsVacuum.apply_zero (H := realHeisenberg (realSigns E s₀)), one_smul]
  have h_zero : V₀.projReal (T 0 (V.ω g (V.projReal f))) =
      ∫ c, (realVac c ^ 2 * 2 ^ Fintype.card (InfinitePlace E × p)) •
        V₀.projReal (N c f) ∂normalizedVolume _ := by
    have h0 := key 0 V₀.projReal
    simp only [star_zero, zero_dotProduct, neg_zero, Complex.exp_zero, one_smul,
      h_proj_idem] at h0
    have hN0 : N 0 = T 0 ∘L V.ω g := by
      dsimp only [N]
      rw [realVec.map_zero, mulVec_zero]
    rw [hN0, ContinuousLinearMap.comp_apply] at h0
    exact h0
  rw [h_zero]
  exact key a 1

/-- Let `T` obey the law of a mixed model (`IsMixedLaw`) for the splitting `D`, and let `g` be
adapted to `t` (`IsAdapted`). Then there is a bounded map `L` between the Fock spaces of `V` and
`V₀` with `T 0 (ω(g)(v ⊗ f)) = L v ⊗ T 0 (ω(g) P f)`, where `P` is the projection on the real
vacuum and `⊗` stands for `New.Space.integrated`. -/
lemma IsAdapted.exists_apply_zero_omega_integrated_eq (hT : D.IsMixedLaw T) {g : G E s}
    {t : GL p (𝔸 E)} (hg : D.IsAdapted g t) :
    ∃ L : Model (realHeisenberg (realSigns E s)) →L[ℂ] Model (realHeisenberg (realSigns E s₀)),
      ∀ (v : Model (realHeisenberg (realSigns E s))) (f : 𝒮 V),
      T 0 (V.ω g (V.integrated v f)) = V₀.integrated (L v) (T 0 (V.ω g (V.projReal f))) := by
  -- L is determined by the images K y of the translated vacua ρ(y) vac. Let g `realVec y` have the
  -- parts c, w, b along l, V₀, k. The law gives the character `χ y` and ϱ(w), and
  -- `omega_projReal_of_isMixedLaw` gives a Gaussian in `a y`, the real vector t* c.
  let a (y : InfinitePlace E × n → ℂ) : InfinitePlace E × p → ℂ :=
    realMatrix (t.valᴴ * D.lCoord * g.adeleMatrix) *ᵥ y
  let χ (y : InfinitePlace E × n → ℂ) : ℂ :=
    (adelicHeisenberg E 1).β ((D.lCoord * g.adeleMatrix) *ᵥ realVec y)
      ((D.kCoord * g.adeleMatrix) *ᵥ realVec y)
  let K (y : InfinitePlace E × n → ℂ) : fockSpace (realSigns E s₀) :=
    (χ y * exp (-(star (a y) ⬝ᵥ a y))) •
      realHeisenbergOp (realMatrix (D.iCoord * g.adeleMatrix) *ᵥ y) Fock.vacVector
  have h_vec (M : Matrix p n (𝔸 E)) :
      Continuous fun y : InfinitePlace E × n → ℂ ↦ M *ᵥ realVec y :=
    continuous_pi fun i ↦ continuous_sum Finset.univ fun j _ ↦
      continuous_const.mul ((continuous_apply j).comp continuous_realVec)
  have hχ_cont : Continuous χ := (adelicHeisenberg E 1).cont.comp₂ (h_vec _) (h_vec _)
  have ha_cont : Continuous a :=
    continuous_pi fun i ↦ continuous_sum Finset.univ fun j _ ↦
      continuous_const.mul (continuous_apply j)
  have hi_cont : Continuous fun y : InfinitePlace E × n → ℂ ↦
      realMatrix (D.iCoord * g.adeleMatrix) *ᵥ y :=
    continuous_pi fun i ↦ continuous_sum Finset.univ fun j _ ↦
      continuous_const.mul (continuous_apply j)
  have h_dot_cont : Continuous fun y : InfinitePlace E × n → ℂ ↦ star (a y) ⬝ᵥ a y :=
    continuous_sum Finset.univ fun i _ ↦
      (Complex.continuous_conj.comp ((continuous_apply i).comp ha_cont)).mul
        ((continuous_apply i).comp ha_cont)
  have hK_cont : Continuous K :=
    (hχ_cont.mul h_dot_cont.neg.cexp).smul
      ((Heisenberg.IsVacuum.heisenbergRep (H := realHeisenberg (realSigns E s₀))).cont.comp
        (hi_cont.prodMk continuous_const))
  have hK_bdd (y : InfinitePlace E × n → ℂ) :
      ‖K y‖ ≤ ‖(Fock.vacVector : fockSpace (realSigns E s₀))‖ := by
    -- `χ y` has modulus one, the Heisenberg operator is isometric and the Gaussian is at most 1.
    have h_gauss_le : Real.exp (-(star (a y) ⬝ᵥ a y).re) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr ((sq_nonneg ‖a y‖).trans (norm_sq_le_re_star_dotProduct_self (a y))))
    rw [show ‖K y‖ = Real.exp (-(star (a y) ⬝ᵥ a y).re) *
        ‖(Fock.vacVector : fockSpace (realSigns E s₀))‖ by
      simp only [K, χ, norm_smul, norm_mul, norm_eq_one, one_mul, norm_exp, neg_re, Rep.norm_map]]
    exact mul_le_of_le_one_left (norm_nonneg _) h_gauss_le
  -- `exists_lift` gives a bounded `L` with `M ∘ L = N` once `M (K y) = N (ρ(y) vacuum)` for all
  -- `y`.
  obtain ⟨L, hL⟩ := exists_lift (H := realHeisenberg (realSigns E s)) (Y := 𝒮 V₀) hK_cont hK_bdd
  refine ⟨L, fun v f ↦ ?_⟩
  set u : 𝒮 V := V.ω g (V.projReal f)
  have h_translate (y : InfinitePlace E × n → ℂ) :
      V₀.integrated (K y) (T 0 u) =
        T 0 (V.ω g (V.integrated (realHeisenbergOp y Fock.vacVector) f)) := by
    let c : p → 𝔸 E := (D.lCoord * g.adeleMatrix) *ᵥ realVec y
    have h_gauss : T c u = exp (-(star (a y) ⬝ᵥ a y)) • V₀.projReal (T 0 u) := by
      rw [← hg.omega_projReal_of_isMixedLaw hT (a y) f]
      congr 1
      dsimp only [a, c]
      rw [realVec_realMatrix_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        ← coe_units_inv, ← conjTranspose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        conjTranspose_one, Matrix.one_mul]
    dsimp only [K]
    rw [V₀.integrated.map_smul, _root_.smul_apply, integrated_realHeisenbergOp,
      realVec_realMatrix_mulVec, mul_smul, ← (V₀.ϱ _).map_smul, ← h_gauss,
      integrated_realHeisenbergOp, omega_rho, hT 0 (g.adeleMatrix *ᵥ realVec y) u]
    simp only [zero_add, mulVec_mulVec]
    rfl
  exact (hL (V₀.integrated.flip (T 0 u)) (T 0 ∘L V.ω g ∘L V.integrated.flip f) h_translate v).symm

end New.Space.Splitting
