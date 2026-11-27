module

public import Lib.GaloisRep.BaseChange.ShintaniLift
public import Lib.GaloisRep.LocalGlobal.IwahoriCompatibility

/-!
# Tame exponents of inertia and local-global compatibility for labelled forms

Let `w` be a finite place of `E` whose residue field `k_w` has order `q`, let `A` be a valuation
subring of an algebraic closure `Ω` lying over `w`, and let `T` be an injective complex-valued
multiplicative character of an algebraically closed extension `K` of `k_w`.

## Main definitions and results

* `New.GaloisRep.IsTameExponent w A T f s a`: the inertial element `s` moves a `(q ^ f - 1)`-th root
  of a uniformiser by the root of unity that `T` reads as `exp (2πi a / (q ^ f - 1))`.
* `New.GaloisRep.IsLabelledAt`: for a polynomial `c` over the residue field, the polynomial with
  roots `ιℓ ((T ^ a) x)` satisfies a given condition at each such `s`. Here `x` runs over the roots
  of `c`, `ιℓ` is the fixed map from `ℂ` to `PadicAlgCl ℓ`, and `T ^ a` is the `a`-th power of the
  character `T`.
* `New.GaloisRep.IsTameExponent.pow_apply_charName`: comparison with the local Artin map, for
  characters of `k_wˣ`.
* `New.GaloisRep.exists_isTameExponent`: exponents exist when `f` is a factorial.
* `New.GaloisRep.Attached.isLabelledAt`: if an eigenform has, at a split place `w`, a type for
  `GL n` of the residue field given by a label (`New.HasProductLabel`: a polynomial `c` of degree
  `d` and characters `χ l` with multiplicities `t l`, where `d + ∑ l, t l` is the rank and the roots
  of `c` and the names of the `χ l` are all distinct), then inertia at `w` acts on the attached
  Galois representation through the tame characters given by the roots of the polynomial of the
  label (`New.GaloisRep.IsLabelledAt`, `New.GaloisRep.IsTameExponent`). The proof uses base changes
  of prime degree in which `w` is inert to reduce to the case where `c` splits into linear factors.
  That case follows from `New.GaloisRep.Attached.local_global_of_eigencharacter` applied to local
  units.

Notions from other files:
* `New.IsPlaceOver A w`: the valuation subring `A` of `Ω` lies over `w`, that is, an integer of `E`
  is in the maximal ideal of `A` exactly when it lies in `w`.
* `New.Cohomology.centrePrime Ω A`: the integers of `Ω` that lie in the maximal ideal of `A`.
* `New.charName T χ`: the unit of `k_w` that names the character `χ` of `k_wˣ`; the map `χ ↦ x_χ` is
  an isomorphism from the character group of `k_wˣ` to `k_wˣ` that depends on `T`.
* `New.GaloisRep.PolyKillsAt r A s Q`: the polynomial `Q` kills `r s` if `ℓ` is a unit at `A`, and
  kills the action of `s` on the periods of `r` if `A` lies above `ℓ`.

## Relation to the literature

Known result: Local-global compatibility at tame level, away from ℓ and at ℓ. Here it is proved only
at split places, for depth-zero types induced from a squarefree type and characters of the
determinant. It is stated as polynomials that kill inertia elements, without the local Langlands
correspondence, and it is reduced by cyclic base change to the case of sorted tame Iwahori
eigencharacters. Source: Harris, Taylor, The geometry and cohomology of some simple Shimura
varieties (2001); Taylor, Yoshida, J. Amer. Math. Soc. 20 (2007); Barnet-Lamb, Gee, Geraghty,
Taylor, Local-global compatibility for l = p, II (2014), Thm 1.1.

See also `Lib.ClassField.Local.ArtinMap`.
-/

@[expose] public section

/-! ## Tame exponents of inertial elements and inertia acting through labels -/

namespace New.GaloisRep

open NumberField Polynomial Cohomology Ideal Quotient IsAlgClosed IsLocalRing RingHom algebraMap

variable {E : Type} [Field E] [EmbeddedNumberField E] (w : FinPlace E) (A : ClosurePlace)
  {K : Type} [Field K] [Algebra (ResField w) K] (T : MulChar K ℂ) (f : ℕ) (s : Gal(Ω/E)) (a : ℕ)

/-- A ring homomorphism `g : 𝓞 E →+* R` to a field killing `w` factors through `ResField w`. -/
lemma exists_resField_hom {R : Type*} [Field R] (g : 𝓞 E →+* R) (h_le_ker : w.asIdeal ≤ ker g) :
    ∃ j : ResField w →+* R, ∀ x : 𝓞 E, j (algebraMap (𝓞 E) (ResField w) x) = g x :=
  ⟨liftOfSurjective _ (algebraMap_ResField_surjective w)
    ⟨g, fun _ hx ↦ h_le_ker (algebraMap_ResField_eq_zero.1 hx)⟩, liftOfSurjective_comp_apply _ _ _⟩

/-- Witness data for `New.GaloisRep.IsTameExponent`. -/
structure IsTameWitness (φ : 𝓞 Ω →+* K) (π : E) (z : Ω) (t : 𝓞 Ω) : Prop where
  centrePrime_le_ker : centrePrime Ω A ≤ ker φ
  commutes (x : 𝓞 E) : φ (algebraMap (𝓞 E) (𝓞 Ω) x) =
    algebraMap (ResField w) K (algebraMap (𝓞 E) (ResField w) x)
  isUniformiser : IsUniformiser A π
  pow_eq : z ^ (w.q ^ f - 1) = algebraMap E Ω π
  coe_eq : (t : Ω) = s z / z
  map_eq : T (φ t) = Complex.exp (2 * Real.pi * Complex.I / (w.q ^ f - 1 : ℕ)) ^ a

/-- `s` has tame exponent `a` at level `f`: `A` lies over `w`, `f ≠ 0`, `s` lies in the inertia
group of `A`, and there is a witness (`New.GaloisRep.IsTameWitness`). -/
structure IsTameExponent : Prop where
  isPlaceOver : IsPlaceOver A w
  level_ne_zero : f ≠ 0
  mem_inertiaGroup : s ∈ inertiaGroup Gal(Ω/E) A
  exists_witness : ∃ (φ : 𝓞 Ω →+* K) (π : E) (z : Ω) (t : 𝓞 Ω),
    IsTameWitness w A T f s a φ π z t

variable {w A f s a}

open Nat

/-- Inertia acts through the tame characters of level `f` given by the roots of `c`: whenever `s`
has tame exponent `a`, `P` holds for `s` and `∏ x, (X - ιℓ ((T ^ a) x))` over the roots of `c`. -/
def IsLabelledAt {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] (A : ClosurePlace) (T : MulChar K ℂ) (f : ℕ)
    (P : Gal(Ω/E) → (PadicAlgCl ℓ)[X] → Prop) (c : (ResField w)[X]) : Prop :=
  ∀ ⦃s : Gal(Ω/E)⦄ ⦃a : ℕ⦄,
    IsTameExponent w A T f s a → P s ((c.aroots K).map fun x : K ↦ X - C (ιℓ ((T ^ a) x))).prod

/-- Comparison of `IsTameExponent` with the local Artin map: if `s` has tame exponent `a` and is
the local Artin symbol of a unit `u`, then `(T ^ a) (charName T χ) = χ (residue u)`. -/
lemma IsTameExponent.pow_apply_charName [IsFaithfulMulChar K T]
    {hs_dec : s ∈ decompGroup Gal(Ω/E) A} (h_exp : IsTameExponent w A T f s a)
    {u : (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w)ˣ}
    (hu : Valued.v u.val = 1) (h_artin : localArtin Gal(Ω/E) A w u = ⟦⟨s, hs_dec⟩⟧)
    (χ : MulChar (ResField w) ℂ) :
    (T ^ a) ((charName T χ).val : ResField w) = χ (residue (LocInt w) ⟨u, hu.le⟩) := by
  obtain ⟨ρ, hρ⟩ := h_exp.exists_witness
  obtain ⟨π, z, t, hw⟩ := hρ
  obtain ⟨k, hk⟩ : w.q - 1 ∣ w.q ^ f - 1 := w.q.sub_one_dvd_pow_sub_one f
  obtain ⟨x, hx⟩ := algebraMap_ResField_surjective w (residue (LocInt w) ⟨u, hu.le⟩)
  have h_res : ρ t ^ k = algebraMap (ResField w) K (residue (LocInt w) ⟨u, hu.le⟩) := by
    have h_sym : A.valuation (s (z ^ k) / z ^ k - algebraMap E Ω x) < 1 :=
      (h_exp.isPlaceOver.valuation_sub_lt_one_iff_of_localArtin_eq hw.isUniformiser hu h_artin
        (by rw [← pow_mul', ← hk, hw.pow_eq])).1 (residue_eq_iff_valuation_sub_lt_one.1 hx.symm)
    rw [map_pow, ← div_pow, ← hw.coe_eq] at h_sym
    have h_cong : t ^ k - algebraMap (𝓞 E) (𝓞 Ω) x ∈ centrePrime Ω A := mem_centrePrime.2 h_sym
    simpa [← hx, hw.commutes, sub_eq_zero] using hw.centrePrime_le_ker h_cong
  rw [← thetaChar_charName T χ, ← h_res]
  exact (thetaChar_apply_pow T Finite.one_lt_card (algebraMap_pow_card_pred_eq_one _)
    (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow h_exp.level_ne_zero w.one_lt_q))
    (by rwa [card_ResField]) hw.map_eq).symm

/-- Every root `x` in `K` of a label `c` of degree `r` over `k_w` satisfies `x ^ (q ^ r! - 1) = 1`
and `x ^ (q ^ d - 1) = 1` for some `1 ≤ d ≤ r`. -/
lemma _root_.New.IsLabel.root_pow_eq_one {c : (ResField w)[X]} {r : ℕ} (h_label : IsLabel r c)
    {x : K} (hx : aeval x c = 0) :
    x ^ (w.q ^ (r)! - 1) = 1 ∧ ∃ d ∈ Set.Icc (1 : ℕ) r, x ^ (w.q ^ d - 1) = 1 := by
  obtain ⟨hmonic, -, hdeg, hc0⟩ := h_label
  set P : (ResField w)[X] := minpoly (ResField w) x
  have hP : Irreducible P := minpoly.irreducible ⟨c, hmonic, hx⟩
  have hd_le : P.natDegree ≤ r := (natDegree_le_natDegree (minpoly.min _ _ hmonic hx)).trans_eq hdeg
  have h_pow {n : ℕ} (hn : n ≠ 0) (hd : P.natDegree ∣ n) : x ^ (w.q ^ n - 1) = 1 := by
    rw [pow_pred_eq_one_iff (one_lt_pow₀ w.one_lt_q hn), ← card_ResField,
      root_pow_card_pow_eq_self_iff hP (minpoly.aeval _ x)]
    exact ⟨fun h0 ↦ hc0 (by simpa [h0, aeval_def, eval₂_at_zero] using hx), hd⟩
  exact ⟨h_pow r.factorial_ne_zero (dvd_factorial hP.natDegree_pos hd_le),
    P.natDegree, ⟨hP.natDegree_pos, hd_le⟩, h_pow hP.natDegree_pos.ne' dvd_rfl⟩

/-- Extend `ResField w →+* K` to `𝓞 Ω →+* K` killing `centrePrime Ω A` when `K` is alg. closed. -/
private lemma exists_ringHom_centrePrime_le_ker [IsAlgClosed K] (hA : IsPlaceOver A w) :
    ∃ ρ : 𝓞 Ω →+* K, centrePrime Ω A ≤ ker ρ ∧ ∀ x : 𝓞 E,
      ρ (algebraMap (𝓞 E) (𝓞 Ω) x) =
        algebraMap (ResField w) K (algebraMap (𝓞 E) (ResField w) x) := by
  have := hA.centrePrime_liesOver; let := Quotient.field w.asIdeal
  algebraize [(algebraMap (ResField w) K).comp
    (Ideal.Quotient.lift w.asIdeal (algebraMap (𝓞 E) (ResField w))
      (fun _ hx ↦ algebraMap_ResField_eq_zero.2 hx))]
  let : Module.IsTorsionFree (𝓞 E ⧸ w.asIdeal) K :=
    DivisionSemiring.to_moduleIsTorsionFree
  let : Module.IsTorsionFree (𝓞 E ⧸ w.asIdeal) (𝓞 Ω ⧸ centrePrime Ω A) :=
    DivisionSemiring.to_moduleIsTorsionFree
  let j : (𝓞 Ω ⧸ centrePrime Ω A) →ₐ[𝓞 E ⧸ w.asIdeal] K := IsAlgClosed.lift
  exact ⟨j.toRingHom.comp (Ideal.Quotient.mk _), fun x hx ↦ by
    change j (Ideal.Quotient.mk _ x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero],
    fun x ↦ j.commutes (Ideal.Quotient.mk w.asIdeal x)⟩

/-- At level `f !` over `A` above `w` (with `IsFaithfulMulChar K T`): (a) some inertia element has
tame exponent `1`; (b) every inertia element `s` has a tame exponent `a`, coprime to `q ^ f ! - 1`
when `s = hA.tameGenerator`. -/
lemma exists_isTameExponent [IsFaithfulMulChar K T] (hA : IsPlaceOver A w) (f : ℕ) :
    (∃ s : inertiaGroup Gal(Ω/E) A, IsTameExponent w A T (f)! s.val 1) ∧
    ∀ s ∈ inertiaGroup Gal(Ω/E) A, ∃ a : ℕ,
      IsTameExponent w A T (f)! s a ∧ (s = hA.tameGenerator → a.Coprime (w.q ^ (f)! - 1)) := by
  let N : ℕ := w.q ^ f.factorial - 1
  have hN_res : NeZero (N : ResField w) := let := Fintype.ofFinite (ResField w);
    ⟨by simp [N, ← card_ResField, f.factorial_ne_zero, NeZero.pos]⟩
  have : NeZero (N : K) := .of_faithfulSMul (ResField w) K N
  have hN : NeZero N := hN_res.of_neZero_natCast
  have hN_val : A.valuation N = 1 := hA.valuation_natCast_eq_one_iff.2 fun hmem ↦
    hN_res.out (mod_cast algebraMap_ResField_eq_zero.2 hmem)
  obtain ⟨ρ, hρ_cen, hρ_int⟩ := exists_ringHom_centrePrime_le_ker (K := K) hA
  obtain ⟨π, z, hπz⟩ := hA.exists_isPrimitiveRoot_tameGenerator_smul_div hN_val
  obtain ⟨hπ, hz, hζ⟩ := hπz
  have hρζ : IsPrimitiveRoot (ρ hζ.toInteger) N := isRoot_cyclotomic_iff.1 <|
    map_cyclotomic N ρ ▸ (isRoot_cyclotomic_iff.2 hζ.toInteger_isPrimitiveRoot).map ρ
  obtain ⟨j, -, hj, hTj⟩ :
      ∃ j < N, j.Coprime N ∧ T (ρ hζ.toInteger) ^ j = Complex.exp (2 * Real.pi * Complex.I / N) :=
    (hρζ.map_of_injective IsFaithfulMulChar.injective).isPrimitiveRoot_iff.1
      (Complex.isPrimitiveRoot_exp N hN.out)
  have hζj : IsPrimitiveRoot ((hA.tameGenerator • z / z) ^ j) N := hζ.pow_of_coprime j hj
  have tame_of_eq (s : inertiaGroup Gal(Ω/E) A) (a : ℕ)
      (hsa : ((hA.tameGenerator • z / z) ^ j) ^ a = s.val z / z) :
      IsTameExponent w A T f.factorial s a :=
    ⟨hA, f.factorial_ne_zero, s.2, ρ, ⟨π, z, (hζ.toInteger ^ j) ^ a,
      { centrePrime_le_ker := hρ_cen, commutes := hρ_int, isUniformiser := hπ,
        pow_eq := hz, coe_eq := hsa, map_eq := by simp only [map_pow, hTj, N] }⟩⟩
  refine ⟨⟨hA.tameGenerator ^ j, tame_of_eq _ 1 <|
    (pow_one _).trans (inertia_pow_smul_div hA.tameGenerator.2 hN_val hz j).symm⟩, fun s hs ↦ ?_⟩
  obtain ⟨a, -, ha⟩ := hζj.eq_pow_of_pow_eq_one (ξ := s z / z) (by simp [div_pow, ← map_pow, hz])
  refine ⟨a, tame_of_eq ⟨s, hs⟩ a ha, fun hs_gen ↦ (hζj.pow_iff_coprime hN.pos a).1 ?_⟩
  rwa [ha, hs_gen]

/-- Tame exponents after an unramified base change. -/
private lemma IsTameExponent.of_unramified {L : Type} [Field L] [EmbeddedNumberField L]
    [Algebra E L] [IsScalarTower E L Ω] {u : FinPlace L} [Algebra (ResField w) (ResField u)]
    {p g : ℕ} {σ : Gal(Ω/L)} (h_exp : IsTameExponent w A T (p * g) (σ.restrictScalars E) a)
    (h_below : u.below E = w) (hAu : IsPlaceOver A u) (h_ram : u.asIdeal.ramificationIdx (𝓞 E) = 1)
    (hq : w.q ^ p = u.q)
    (hj : ∀ x : 𝓞 E, algebraMap (ResField w) (ResField u) (algebraMap (𝓞 E) (ResField w) x) =
      algebraMap (𝓞 L) (ResField u) (algebraMap (𝓞 E) (𝓞 L) x)) :
    ∃ _ : Algebra (ResField u) K,
      IsScalarTower (ResField w) (ResField u) K ∧ IsTameExponent u A T g σ a := by
  subst h_below
  obtain ⟨ρ, hρ⟩ := h_exp.exists_witness
  obtain ⟨π, z, t, hw⟩ := hρ
  obtain ⟨i, hi⟩ := exists_resField_hom u (ρ.comp (algebraMap (𝓞 L) (𝓞 Ω))) <| by
    rw [hAu.centrePrime_liesOver.over]; exact fun _ hx ↦ hw.centrePrime_le_ker hx
  algebraize [i]
  refine ⟨i.toAlgebra, .of_algebraMap_eq fun y ↦ ?_,
    ⟨hAu, right_ne_zero_of_mul h_exp.level_ne_zero, h_exp.mem_inertiaGroup,
      ρ, ⟨algebraMap E L π, z, t,
        { centrePrime_le_ker := hw.centrePrime_le_ker, commutes := fun x ↦ (hi x).symm,
          isUniformiser := by rw [hAu.isUniformiser_iff, ← (u.below E).valuation_liesOver L,
            h_exp.isPlaceOver.isUniformiser_iff.1 hw.isUniformiser, h_ram, pow_one],
          pow_eq := by rw [← hq, ← pow_mul, hw.pow_eq, IsScalarTower.algebraMap_apply E L Ω],
          coe_eq := hw.coe_eq, map_eq := by rw [← hq, ← pow_mul, hw.map_eq] }⟩⟩⟩
  obtain ⟨x, rfl⟩ := algebraMap_ResField_surjective _ y
  show algebraMap (ResField (u.below E)) K _ = i _
  rw [hj, hi, comp_apply, ← IsScalarTower.algebraMap_apply (𝓞 E) (𝓞 L), hw.commutes]

end New.GaloisRep

/-! ## Local-global compatibility at a split place for a labelled form -/

section LabelCompatibility

open NumberField Polynomial Ideal Finset Function Module Fin New QZChar

/-- Mapping `y ↦ X - C (g y)` over the roots in `K` of `∏ i, (X - C (α i)) ^ e i`. -/
private lemma prod_map_aroots_prod_X_sub_C_pow {ι k K L : Type*} [Fintype ι] [Field k] [Field K]
    [Algebra k K] [CommRing L] (α : ι → k) (e : ι → ℕ) (g : K → L) :
    (((∏ i : ι, (X - C (α i)) ^ e i).aroots K).map fun y ↦ X - C (g y)).prod =
      ∏ i : ι, (X - C (g (algebraMap k K (α i)))) ^ e i := by
  rw [aroots, Polynomial.map_prod]
  simp_rw [Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]
  rw [roots_prod _ _ (prod_ne_zero_iff.2 fun i _ ↦ ((monic_X_sub_C _).pow _).ne_zero)]
  simp [Multiset.map_bind, Multiset.map_nsmul, Multiset.prod_nsmul]

/-- Existence of a prime-degree cyclic base change in which a split place `w` is inert. -/
private lemma exists_inertStep {E : Type} [Field E] [EmbeddedNumberField E] [CMType E] [WeilData E]
    {w : FinPlace E} {A : ClosurePlace} {p : ℕ} (hw : w.IsSplit) (hA : IsPlaceOver A w)
    (hp : p.Prime) :
    ∃ (μ : QZChar Gal(Ω/E)) (u : FinPlace (stepField μ)),
      (∃ η : (LocField w)ˣ →* Multiplicative QZ, GaloisRep.IsStepOfLocalChar A η p μ u) ∧
      inertiaGroup Gal(Ω/E) A ≤ ker (symmetrise μ) ∧
      u.asIdeal.ramificationIdx (𝓞 E) = 1 ∧ w.q ^ p = u.q := by
  have : Fact p.Prime := ⟨hp⟩
  let η : (LocField w)ˣ →* Multiplicative QZ :=
    .mk' (fun x ↦ .ofAdd (.ofZMod p (Valued.v x.val).log)) (by simp)
  have hη_unit (x : (LocField w)ˣ) (hx : Valued.v x.val = 1) : η x = 1 := by simp [η, hx]
  obtain ⟨μ, u, h_step⟩ := GaloisRep.exists_isStepOfLocalChar hw hA hp η
    (DFunLike.ne_iff.2 ⟨uniformizer w, by simp [η, map_eq_zero_iff]⟩)
    (fun x ↦ by simp [η, ← ofAdd_nsmul, ← map_nsmul, ZMod.natCast_self])
    (fun x hx ↦ by rw [map_pow, hη_unit x hx, one_pow])
  have h_unram : inertiaGroup Gal(Ω/E) A ≤ ker (symmetrise μ) :=
    (hA.artinAt_units_trivial_iff_inertiaGroup_le (symmetrise μ)).1
      fun x hx ↦ (h_step.abelianLift_symmetrise_artinAt x).trans (hη_unit x hx)
  have h_ram : u.asIdeal.ramificationIdx (𝓞 E) = 1 :=
    (hA.ramification_in_tower (ker (symmetrise μ)) h_step.isPlaceOver).2.1 h_unram
  refine ⟨μ, u, ⟨η, h_step⟩, ⟨h_unram, h_ram, ?_⟩⟩
  have h_below : u.below E = w := (h_step.below_eq_iff u).2 rfl
  have h_in : u.asIdeal.inertiaDeg (𝓞 E) = p := by
    simpa [h_below, h_step.below_eq_iff, h_ram, h_step.finrank_eq] using
      u.ncard_mul_ramificationIdx_mul_inertiaDeg (K := E)
  simp [← h_below, ← h_in, absNorm_pow_inertiaDeg]

variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E n : Type} [Nonempty n] [Field E] [CMType E]
  [EmbeddedNumberField E] [Fintype n] [DecidableEq n] {κ : Weight E}
  {f : Gf E n → WeylIndex n κ.1 → ℂ} {P : FinPlace E → ℂ[X]} {r : GalRep ℓ E n}
  {w : FinPlace E} {A : ValuationSubring Ω} {hw : star w ≠ w} {K : Type} [Field K]
  [Algebra (ResField w) K] {T : MulChar K ℂ} [IsFaithfulMulChar K T] {s d : ℕ}
  {c : (ResField w)[X]} {χ : Fin s → MulChar (ResField w) ℂ} {t : Fin s → ℕ} [WeilData E]

/-- Level-`1` case of `New.GaloisRep.Attached.isLabelledAt`, where `c` splits linearly. -/
private lemma New.GaloisRep.Attached.isLabelledAt_one (hf : f ∈ (stdSpace E n).forms κ)
    (he : IsEigenform f P) (hr : Attached P r) (hA : IsPlaceOver A w)
    (h_prod_label : HasProductLabel f hw T d c χ t)
    (h_roots : ∀ x : K, aeval x c = 0 → x ^ (w.q - 1) = 1) :
    IsFiniteTypeAt r A ∧
    HasJumpsAt r A (jumps κ (Fintype.card n)) ∧
    IsLabelledAt A T 1 (PolyKillsAt r A)
      (c * ∏ l : Fin s, (X - C (charName T (χ l)).val) ^ t l) := by
  obtain ⟨h_label, h_sep, h_deg, h_has⟩ := h_prod_label
  obtain ⟨ψ, rfl⟩ := h_label.exists_eq_prod_charName_of_root_pow_card_eq T fun y hy ↦ by
    rw [card_ResField]; exact ((pow_pred_eq_one_iff w.one_lt_q).1 (h_roots y hy)).2
  have h_inj : Injective (append ψ χ) := .of_comp (f := fun η ↦ (charName T η).val) <| by
    simpa [Function.comp_def, ← separable_prod_X_sub_C_iff, prod_univ_add] using h_sep
  let ρ := Patching.localFormRep (stdSpace E n) κ hw
  have h_act (g : GL n (LocField w)) : (ρ (reindexGL (Fintype.equivFin n) g) ⟨f, hf⟩).val =
      rightRegular ℂ (Gf E n) (WeylIndex n κ.1 → ℂ) (ofSplitPlace hw g) f := by
    simp [ρ, Patching.localFormRep, Patching.embedAtSplit]
  let red := intGL.map (n := n) (IsLocalRing.residue (Valued.integer (LocField w)))
  have h_red (k : intGL n (Valued.integer (LocField w))) : red k = reduceGL k := rfl
  have h_fix : ∀ k, red k = 1 → ρ (reindexGL (Fintype.equivFin n) k.val) ⟨f, hf⟩ = ⟨f, hf⟩ :=
    fun k hk ↦ Subtype.ext ((h_act k.val).trans (h_has.1 k (h_red k ▸ hk)))
  have h_lift : ∀ g : GL n (ResField w), red (surjInv reduceGL_surjective g) = g :=
    fun g ↦ (h_red _).trans (surjInv_eq reduceGL_surjective g)
  have h_sum : ∑ᶠ g : GL n (ResField w),
      star ((∏ b, (detChar (append ψ χ b)).rankPart (append 1 t b)).evalGL g) •
        ρ (reindexGL (Fintype.equivFin n) (surjInv reduceGL_surjective g).val) ⟨f, hf⟩ ≠ 0 := by
    intro h0
    have h1 := congrArg ((stdSpace E n).forms κ).subtype h0
    rw [map_finsum _ (Set.toFinite _), map_zero] at h1
    exact h_has.2 (by simpa [h_act, prod_univ_add, labelChar_X_sub_C] using h1)
  obtain ⟨z, hz, ξ, h_z⟩ := exists_sorted_of_detChar (ρ := ρ) (x := ⟨f, hf⟩) (v_uniformizer w)
    isUnitary_localFormRep (Fintype.equivFin n) h_inj (m := append 1 t)
    (by simpa [sum_univ_add] using h_deg) h_fix h_lift h_sum
  obtain ⟨lab, h_eig, h_sorted, h_lab⟩ := h_z
  have hez : IsEigenform z.val P := he.of_mem_cyclicSpan hz h_eig.ne_zero
  obtain ⟨h_fin, h_jump, -⟩ := hr.local_global_of_eigencharacter h_eig hez h_sorted hA 1 1 0
    (by simp [← mem_inertiaGroup_iff]) (by simp) (by simp)
  refine ⟨h_fin, h_jump, fun σ a h_tame ↦ ?_⟩
  have hσ := h_tame.mem_inertiaGroup
  obtain ⟨x, hx, hxσ⟩ := hA.exists_localArtin_eq (inv_mem hσ) 0
  have hx_unit : Valued.v x.val = 1 := by simpa using hx
  rw [show (∏ i : Fin d, (X - C (charName T (ψ i)).val)) *
        ∏ l : Fin s, (X - C (charName T (χ l)).val) ^ t l =
      ∏ b : Fin (d + s), (X - C (charName T (append ψ χ b)).val) ^ append 1 t b by
        simp [prod_univ_add], prod_map_aroots_prod_X_sub_C_pow]
  simp_rw [h_tame.pow_apply_charName T hx_unit hxσ]
  rw [← prod_X_sub_C_eq_prod_pow_of_card_fiber h_lab.1 fun i ↦ congrArg ιℓ (h_lab.2 x hx_unit i)]
  exact (hr.local_global_of_eigencharacter h_eig hez h_sorted hA
    ⟨σ, hσ.1⟩ x 0 (inv_mem hσ) hxσ hx).2.2

/-- Level-`g` case (`g ≠ 0`) of `New.GaloisRep.Attached.isLabelledAt`. -/
private lemma New.GaloisRep.Attached.isLabelledAt_of_root_pow_eq_one {g : ℕ}
    (hf : f ∈ (stdSpace E n).forms κ) (he : IsEigenform f P) (hr : Attached P r)
    (hA : IsPlaceOver A w) (h_prod_label : HasProductLabel f hw T d c χ t) (hg : g ≠ 0)
    (h_roots : ∀ x : K, aeval x c = 0 → x ^ (w.q ^ g - 1) = 1) :
    IsFiniteTypeAt r A ∧
    HasJumpsAt r A (jumps κ (Fintype.card n)) ∧
    IsLabelledAt A T g (PolyKillsAt r A)
      (c * ∏ l : Fin s, (X - C (charName T (χ l)).val) ^ t l) := by
  induction g using induction_on_primes generalizing E with
  | zero => exact absurd rfl hg
  | one => exact hr.isLabelledAt_one hf he hA h_prod_label (by simpa using h_roots)
  | prime_mul p g hp ih =>
    obtain ⟨h_label, h_sep, h_deg, h_has⟩ := h_prod_label
    obtain ⟨μ, u, ⟨_, h_step⟩, h_inert⟩ := exists_inertStep hw hA hp
    obtain ⟨h_unram, h_ram, hq⟩ := h_inert
    obtain ⟨_⟩ := h_step.nonempty_weilData
    have : IsStep (stepField μ) (ideleChar μ) := h_step.isStep
    have hAu : IsPlaceOver A u := h_step.isPlaceOver
    have h_below : u.below E = w := (h_step.below_eq_iff u).2 rfl
    obtain ⟨j₀, h_res⟩ := GaloisRep.exists_resField_hom w
      ((algebraMap (𝓞 (stepField μ)) (ResField u)).comp (algebraMap (𝓞 E) _))
      fun _ hx ↦ algebraMap_ResField_eq_zero.2 (by rwa [← h_below] at hx)
    algebraize [j₀]
    let j : ResField w →+* ResField u := algebraMap (ResField w) (ResField u)
    have h_res_rank : finrank (ResField w) (ResField u) = p := Nat.pow_right_injective w.one_lt_q <|
      by show w.q ^ _ = w.q ^ p; rw [hq, ← card_ResField, ← card_ResField, ← natCard_eq_pow_finrank]
    -- Given any `ResField w`-embedding `ResField u → K`, Shintani base change descends to `E`.
    have descend [Algebra (ResField u) K] [IsScalarTower (ResField w) (ResField u) K] :
        (IsFiniteTypeAt r A ∧ HasJumpsAt r A (jumps κ (Fintype.card n))) ∧
        ∃ r' : GalRep ℓ (stepField μ) n, DescendsAt μ r' r A ∧
          IsLabelledAt A T g (PolyKillsAt r' A)
            ((c * ∏ l, (X - C (charName T (χ l)).val) ^ t l).map j) := by
      let χ' (l : Fin s) : MulChar (ResField u) ℂ :=
        (charName T).symm (Units.map j.toMonoidHom (charName T (χ l)))
      have hχ' (l : Fin s) : (charName T (χ' l)).val = j (charName T (χ l)).val := by simp [χ']
      have lift_prod {k' : Type} [Field k'] [Finite k'] [Algebra (ResField w) k'] [Algebra k' K]
          [IsScalarTower (ResField w) k' K] {F : Hall (ResField w)} {F' : Hall k'} (h : Lift ℕ F F')
          {η : Fin s → MulChar k' ℂ}
          (hη : ∀ l, (charName T (η l) : k') = algebraMap (ResField w) k' (charName T (χ l))) :
          Lift ℕ (F * ∏ l, (detChar (χ l)).rankPart (t l))
            (F' * ∏ l, (detChar (η l)).rankPart (t l)) :=
        h.mul (prod_hom_rel .one fun l _ _ h_rest ↦
          .mul (.rankPart_of_hasCommonLift (lift_detChar T (hη l) (t l))) h_rest)
      obtain ⟨f', hf', P', h_f'⟩ := exists_baseChange_hasLabel hw h_step.isSplit
        h_step.below_eq_iff (fun _ ↦ by simp [h_step.abelianLift_artinAt]) h_res
        (h_res_rank.trans h_step.finrank_eq.symm) hf
        (isChar_of_mem_virtualChars
          (lift_prod (lift_labelChar_self T h_label) fun _ ↦ rfl).evalGL_mem_virtualChars)
        (lift_prod (shintani_lift_labelChar (by rwa [h_res_rank]) T h_label) hχ') h_has
      obtain ⟨he', h_bc, h_has'⟩ := h_f'
      obtain ⟨r', hr'⟩ := (sphericalCompat_std u hf' he').1
      have h_sep' : (c.map j * ∏ l, (X - C (charName T (χ' l)).val)).Separable := by
        simpa [hχ', Polynomial.map_prod] using h_sep.map (f := j)
      obtain ⟨h_fin, h_jump, h_lab⟩ := ih hf' he' hr' hAu ⟨h_label.map _, h_sep', h_deg, h_has'⟩
        (right_ne_zero_of_mul hg) fun x hx ↦ by
          rw [← hq, ← pow_mul]
          exact h_roots x ((c.aeval_map_algebraMap (ResField u) x).symm.trans hx)
      have h_down : DescendsAt μ r' r A := h_bc.descendsAt hr' he' he hr A
      refine ⟨⟨h_down.isFiniteTypeAt h_fin, h_down.hasJumpsAt _ h_jump⟩, r', h_down, ?_⟩
      rwa [show c.map j * ∏ l, (X - C (charName T (χ' l)).val) ^ t l =
          (c * ∏ l, (X - C (charName T (χ l)).val) ^ t l).map j by
            simp [hχ', Polynomial.map_prod]] at h_lab
    obtain ⟨h_fin, h_jump⟩ : IsFiniteTypeAt r A ∧ HasJumpsAt r A (jumps κ (Fintype.card n)) := by
      let φ : ResField u →ₐ[ResField w] K := IsAlgClosed.lift
      algebraize [φ.toRingHom]
      have : IsScalarTower (ResField w) (ResField u) K :=
        .of_algebraMap_eq fun y ↦ (φ.commutes y).symm
      exact descend.1
    refine ⟨h_fin, h_jump, fun σ a h_tame ↦ ?_⟩
    have hσ := h_tame.mem_inertiaGroup
    obtain ⟨_, _, h_tame'⟩ := h_tame.of_unramified T
      (σ := { σ with commutes' := fun x ↦ x.property ⟨σ, h_unram hσ⟩ }) h_below hAu h_ram hq h_res
    obtain ⟨-, r', h_down, h_lab⟩ := descend
    exact h_down.polyKillsAt ⟨σ, h_unram hσ,
      (hA.artinAt_trivial_iff_decompGroup_le μ).1 h_step.abelianLift_artinAt hσ.1⟩ _ <| by
        have h_kill := h_lab h_tame'; rwa [aroots_map] at h_kill

/-- Let the Galois representation `r` be attached to the Hecke polynomials `P` of the eigenform `f`
of weight `κ`, which has the label `c` (of degree `d`), `χ l`, `t l` at the split place `w`
(`New.HasProductLabel`), and let `A` lie above `w`. Then (a) `r` is of finite type at `A` (finite on
inertia, or potentially crystalline above `ℓ`), (b) it has the Hodge–Tate jumps of `κ`, and (c) if
`σ` has tame exponent `a` at level `d!` (`New.GaloisRep.IsTameExponent`), then
`∏ x, (X - ιℓ ((T ^ a) x))` kills the action of `σ` (`New.GaloisRep.PolyKillsAt`), the product being
over the roots `x` in `K` of `c * ∏ l, (X - x_l) ^ t l`, where `x_l = New.charName T (χ l)`.

This is local-global compatibility at tame level, away from `ℓ` and at `ℓ`, restricted to inertia at
a split place and to depth-zero types.

Clause (c) is a weak form of what this compatibility (Barnet-Lamb–Gee–Geraghty–Taylor, Caraiani)
gives together with the description of the inertial parameters of depth-zero representations of
`GL_n` (see Emerton–Gee–Herzig). -/
lemma New.GaloisRep.Attached.isLabelledAt (hf : f ∈ (stdSpace E n).forms κ) (he : IsEigenform f P)
    (hr : Attached P r) (h_prod_label : HasProductLabel f hw T d c χ t) (hA : IsPlaceOver A w) :
    IsFiniteTypeAt r A ∧
    HasJumpsAt r A (jumps κ (Fintype.card n)) ∧
    IsLabelledAt A T d.factorial (PolyKillsAt r A)
      (c * ∏ l : Fin s, (X - C (charName T (χ l)).val) ^ t l) :=
  hr.isLabelledAt_of_root_pow_eq_one hf he hA h_prod_label d.factorial_ne_zero
    fun _ hx ↦ (h_prod_label.1.root_pow_eq_one hx).1

end LabelCompatibility
