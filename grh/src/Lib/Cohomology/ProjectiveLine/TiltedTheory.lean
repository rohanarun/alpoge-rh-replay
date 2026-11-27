module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Lib.Cohomology.ProjectiveLine.PerfectLine
public import Lib.Cohomology.ProperBaseChange.Theorem

/-!
# The projective line formula for tilted coefficients

Toda cancellation gives a criterion for the line formula, which is applied to the gluing map
for the two discs of the perfect projective line.
-/

@[expose] public section

/-!
## Squares, a criterion for the line formula, and the tilted theory

`New.Variety.TotalH` is total Ext with Yoneda product `New.Variety.TotalH.comp` in diagrammatic
order; `New.Variety.TorsionCoeff.mulClass` is the product with a class valued in the Tate module,
and `New.Variety.sliceEquiv` passes from S ⊗ ℤ[X] to S over the category of points of X.
-/

section TiltedLineFormula


namespace New.Variety

open CategoryTheory Limits Abelian TotalH PerfectLine projLine Finsupp
open ShortComplex (exact_cokernel ShortExact)
open Function hiding comp comp_id comp_assoc

variable {C : Type 1} [Category.{0} C] {W' W Z₀ : AbFunctor C} {S T : ShortComplex (AbFunctor C)}

/-- Let `B → W → I → B` (maps `a`, `b`, `c`) and `I → P → K → I` (maps `d`, `e`, `f`) be two
triangles of additive groups that meet at `I`. The hypothesis `h_first` says that the first is exact
at `W`, `I` and `B`, and `h_second` that the second is exact at `P`, `K` and `I`. If the path
`d ∘ b` from `W` to `P` is bijective, then so is the path `c ∘ f` from `K` to `B`. -/
lemma TotalH.bijective_of_two_triangles {K P I W B : Type*} [AddGroup K] [AddGroup P]
    [AddGroup I] [AddGroup W] [AddGroup B] {a : B → W} {b : W →+ I} {c : I →+ B} {d : I →+ P}
    {e : P → K} {f : K →+ I} (h_first : Exact a b ∧ Exact b c ∧ Exact c a)
    (h_second : Exact d e ∧ Exact e f ∧ Exact f d) (h_bij : Bijective (d.comp b)) :
    Bijective (c.comp f) := by
  obtain ⟨hab, hbc, hca⟩ := h_first
  obtain ⟨hde, hef, hfd⟩ := h_second
  obtain ⟨h_inj, h_surj⟩ := h_bij
  -- As `d ∘ b` is onto, `d` is onto, so `e = 0` and `f` is injective; as `d ∘ b` is injective,
  -- `a = 0` and `c` is onto.
  have h_e_zero : ∀ p, e p = 0 :=
    h_surj.forall.2 fun w ↦ hde.apply_apply_eq_zero (b w)
  have h_zero_of_db (w : W) (hw : d (b w) = 0) : w = 0 := (injective_iff_map_eq_zero _).1 h_inj w hw
  constructor
  · -- If `c (f x) = 0` then `f x = b w` with `d (b w) = d (f x) = 0`; so `w = 0` and `f x = 0`.
    refine (injective_iff_map_eq_zero (c.comp f)).2 fun x hx ↦ ?_
    obtain ⟨w, hw⟩ : ∃ w : W, b w = f x := (hbc (f x)).1 hx
    obtain rfl : w = 0 := h_zero_of_db w (by rw [hw, hfd.apply_apply_eq_zero x])
    obtain ⟨p, rfl⟩ := (hef x).1 (by rw [← hw, map_zero])
    exact h_e_zero p
  · -- Write `y = c r` and correct `r` by some `b w` so that it lies in the kernel of `d`.
    intro y
    obtain ⟨r, rfl⟩ : ∃ r : I, c r = y :=
      (hca y).1 (h_zero_of_db (a y) (by rw [hab.apply_apply_eq_zero y, map_zero]))
    obtain ⟨w, hw⟩ : ∃ w : W, d (b w) = d r := h_surj (d r)
    obtain ⟨x, hx⟩ : ∃ x : K, f x = r - b w := (hfd (r - b w)).1 (by simp [hw])
    exact ⟨x, by simp [hx, hbc.apply_apply_eq_zero]⟩

/-- Fix `i : W' ⟶ W`, `δ : W ⟶ W`, `q : W ⟶ X`, a class `η ∈ Ext²(X, Y)` and `ε : Z₀ ⟶ Y`.
The maps `j : B ⟶ X`, `y : Z₀ ⟶ K` and the class `ω ∈ Ext(B, K)` cancel `η` if `j` has a lifting
property and, after any exact functor `Φ` that makes the cokernel of `i` acyclic for a
coefficient `F`, the product with `ω` is onto and `j^* (η m)` determines `ε^* m`. -/
structure IsTodaCancellation {X Y B K : AbFunctor C} (i : W' ⟶ W) (δ : W ⟶ W) (q : W ⟶ X)
    (η : H X Y 2) (ε : Z₀ ⟶ Y) (j : B ⟶ X) (y : Z₀ ⟶ K) (ω : TotalH B K) : Prop where
  /-- If `g` kills `i` and `δ` and `g ≫ r = q ≫ s`, then `j ≫ s` lifts along `r`. -/
  exists_lift {Q R : AbFunctor C} (g : W ⟶ Q) (r : Q ⟶ R) (s : X ⟶ R) (hi : i ≫ g = 0)
    (hδ : δ ≫ g = 0) (hr : g ≫ r = q ≫ s) : ∃ t : B ⟶ Q, t ≫ r = j ≫ s
  /-- After `Φ`, if `j^* (η m) = ω s`, then `ε^* m = y^* s`. -/
  pullback_eq {E : Type 1} [Category.{0} E] (Φ : AbFunctor C ⥤ AbFunctor E) [IsExactFunctor Φ]
    {F : AbFunctor E} (h_acyclic : ∀ n : ℕ, Subsingleton (H (Φ (cokernel i)) F n))
    (m : TotalH (Φ Y) F) (s : TotalH (Φ K) F)
    (h_eq : pullbackAlong (Φ.map j) (comp (TotalH.map Φ η.toTotalH) m) = comp (TotalH.map Φ ω) s) :
    pullbackAlong (Φ.map ε) m = pullbackAlong (Φ.map y) s
  /-- After `Φ`, the product `s ↦ ω s` is onto. -/
  surjective {E : Type 1} [Category.{0} E] (Φ : AbFunctor C ⥤ AbFunctor E) [IsExactFunctor Φ]
    {F : AbFunctor E} (h_acyclic : ∀ n : ℕ, Subsingleton (H (Φ (cokernel i)) F n)) :
    Surjective (comp (F := F) (TotalH.map Φ ω))

/-- After `Φ`, if `j^* (η m) = ω s`, then `ε^* m` and `y^* s` have the same pull-back along
every `τ`. -/
lemma IsTodaCancellation.pullbackAlong_comp_map_eq {X Y B K : AbFunctor C} {i : W' ⟶ W} {δ : W ⟶ W}
    {q : W ⟶ X} {η : H X Y 2} {ε : Z₀ ⟶ Y} {j : B ⟶ X} {y : Z₀ ⟶ K} {ω : TotalH B K}
    (h_toda : IsTodaCancellation i δ q η ε j y ω) {E : Type 1} [Category.{0} E]
    (Φ : AbFunctor C ⥤ AbFunctor E) [IsExactFunctor Φ] {F N : AbFunctor E}
    (h_acyclic : ∀ n : ℕ, Subsingleton (H (Φ (cokernel i)) F n)) (τ : N ⟶ Φ Z₀)
    (m : TotalH (Φ Y) F) (s : TotalH (Φ K) F)
    (h_eq : pullbackAlong (Φ.map j) (comp (TotalH.map Φ η.toTotalH) m) = comp (TotalH.map Φ ω) s) :
    pullbackAlong (τ ≫ Φ.map ε) m = pullbackAlong (τ ≫ Φ.map y) s := by
  rw [← pullbackAlong_pullbackAlong, ← pullbackAlong_pullbackAlong,
    h_toda.pullback_eq Φ h_acyclic m s h_eq]

/-- Let `δ' ≫ i = i ≫ δ` with `i` a monomorphism, and let `Φ` be an exact functor after which the
cokernel of `i` has no Ext into `F` in any degree. Then `Φ` of the map `(i, δ)` out of the
pushout of `δ'` and `i` is an equivalence for `F`: it induces bijections on `Ext(–, F)`. -/
lemma isCohomEquiv_pushout_desc {i : W' ⟶ W} [Mono i] {δ' : W' ⟶ W'} {δ : W ⟶ W}
    (h_comm : δ' ≫ i = i ≫ δ) {E : Type 1} [Category.{0} E] (Φ : AbFunctor C ⥤ AbFunctor E)
    [IsExactFunctor Φ] {F : AbFunctor E}
    (h_acyclic : ∀ n : ℕ, Subsingleton (H (Φ (cokernel i)) F n)) :
    IsCohomEquiv F (Φ.map (pushout.desc i δ h_comm)) := by
  -- `i` and `pushout.inl` have the same acyclic cokernel, so both are equivalences, and
  -- `pushout.inl` followed by `(i, δ)` is `i`.
  have h_eqv {M N : AbFunctor C} (g : M ⟶ N) [Mono g]
      (hg : ∀ k : ℕ, Subsingleton (H (Φ (cokernel g)) F k)) : IsCohomEquiv F (Φ.map g) :=
    (isCohomEquiv_iff_subsingleton (.map ⟨exact_cokernel g⟩ Φ)).2 hg
  have h_sq : IsPushout i δ' (pushout.inr δ' i) (pushout.inl δ' i) :=
    (IsPushout.of_hasPushout δ' i).flip
  let e := cokernel.map i (pushout.inl δ' i) δ' (pushout.inr δ' i) h_sq.w.symm
  have h_iso : IsIso e := isIso_cokernel_map_of_isPushout h_sq
  have h_inl : IsCohomEquiv F (Φ.map (pushout.inl δ' i)) :=
    h_eqv (pushout.inl δ' i) fun k ↦
      (IsCohomEquiv.of_isIso (Φ.map (inv e)) k).surjective.subsingleton
  refine h_inl.comp_iff.1 ?_
  rw [← Φ.map_comp, pushout.inl_desc]
  exact h_eqv i h_acyclic


-- Keeps definitional checks from unfolding the group structure of the Ext groups.
seal addCommGroupH in
/-- Lemma on squares, for short exact `S`, `T`: let `i` be mono with `δ' ≫ i = i ≫ δ`, `z ≫ δ = 0`,
`f : W ⟶ S.X₂` with `δ ≫ f = 0` and `i ≫ f = α₁ ≫ S.f`, and `α` with `α ≫ T.g = α₁ ≫ n` and
`δ' ≫ α = i ≫ κ ≫ T.f`. Let `η` be the extension class of `S` times that of `T` pulled back along
`n`, and set `q = f ≫ S.g` and `ε = z ≫ κ`. Then there are `j : B ⟶ S.X₃`, `y : Z₀ ⟶ K` and
`ω ∈ Ext(B, K)` that cancel `η` (`New.Variety.IsTodaCancellation`): `j` has the lifting property,
and after any exact functor that makes `coker i` acyclic for a coefficient F, the product with `ω`
is onto and `j^*(η m)` determines `ε^* m`. -/
lemma exists_isTodaCancellation {i : W' ⟶ W} [Mono i] {δ' : W' ⟶ W'} {δ : W ⟶ W}
    (h_comm : δ' ≫ i = i ≫ δ) (z : Z₀ ⟶ W) (hz : z ≫ δ = 0) (hS : S.ShortExact) (hT : T.ShortExact)
    (f : W ⟶ S.X₂) (α : W' ⟶ T.X₂) (κ : W ⟶ T.X₁) (n : S.X₁ ⟶ T.X₃) (α₁ : W' ⟶ S.X₁)
    (hα₁ : α₁ ≫ S.f = i ≫ f) (hδf : δ ≫ f = 0) (hα : δ' ≫ α = i ≫ κ ≫ T.f) (hn : α₁ ≫ n = α ≫ T.g) :
    ∃ (B K : AbFunctor C) (j : B ⟶ S.X₃) (y : Z₀ ⟶ K) (ω : TotalH B K),
      IsTodaCancellation i δ (f ≫ S.g) (hS.extClass.comp (H.map T.X₁ n 1 hT.extClass) rfl)
        (z ≫ κ) j y ω := by
  -- Let `σ` be the map `(i, δ)` out of the pushout `P` of `δ'` and `i`. Then `ω` is the class
  -- of `0 → ker σ → P → W → coker → 0`, the product of the classes of its halves `c₁`, `c₂`.
  let σ : pushout δ' i ⟶ W := pushout.desc i δ h_comm
  let ι : Abelian.coimage σ ⟶ W := Abelian.factorThruCoimage σ
  have c₁ : (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).ShortExact :=
    ShortExact.mk (exact_cokernel ι)
  have c₂ : (ShortComplex.mk (kernel.ι σ) (cokernel.π (kernel.ι σ))
      (cokernel.condition (kernel.ι σ))).ShortExact :=
    ShortExact.mk (exact_cokernel (kernel.ι σ))
  let ω : TotalH (cokernel ι) (kernel σ) := comp c₁.extClass.toTotalH c₂.extClass.toTotalH
  have := hS.mono_f
  have := hT.mono_f
  -- `f` maps `c₁` to `S`: it restricts to `β` on the coimage of `σ` and induces `j` on the
  -- cokernel.
  have hδα₁ : δ' ≫ α₁ = i ≫ 0 := by simp [← cancel_mono S.f, reassoc_of% h_comm, hα₁, hδf]
  have h_square :
      CommSq (pushout.desc α₁ 0 hδα₁) (cokernel.π (kernel.ι σ)) S.f (ι ≫ f) :=
    ⟨by ext1 <;> simp [ι, σ, hα₁, hδf]⟩
  let β : Abelian.coimage σ ⟶ S.X₁ := h_square.lift
  have hβ : cokernel.π (kernel.ι σ) ≫ β = pushout.desc α₁ 0 hδα₁ := h_square.fac_left
  have hβf : β ≫ S.f = ι ≫ f := h_square.fac_right
  let j : cokernel ι ⟶ S.X₃ := cokernel.desc ι (f ≫ S.g) (by simp [← reassoc_of% hβf])
  -- `τ = (α, κ ≫ T.f)` maps `c₂` to `T`: it lies over `β ≫ n` and restricts to `u` on the kernel.
  let τ : pushout δ' i ⟶ T.X₂ := pushout.desc α (κ ≫ T.f) hα
  have hτ : τ ≫ T.g = cokernel.π (kernel.ι σ) ≫ β ≫ n := by
    ext1 <;> simp [τ, hn, reassoc_of% hβ]
  obtain ⟨u, hu⟩ : ∃ u : kernel σ ⟶ T.X₁, u ≫ T.f = kernel.ι σ ≫ τ :=
    hT.exact.lift' (kernel.ι σ ≫ τ) (by simp [hτ])
  let y : Z₀ ⟶ kernel σ := kernel.lift σ (z ≫ pushout.inr δ' i) (by simp [σ, hz])
  have hyu : y ≫ u = z ≫ κ := by simp [← cancel_mono T.f, y, τ, hu]
  -- Naturality of the classes of `c₁` and `c₂` gives `j^* η = ω u`.
  have h_nat₁ : c₁.extClass.comp (Ext.mk₀ β) (add_zero 1) =
      (Ext.mk₀ j).comp hS.extClass (zero_add 1) :=
    c₁.extClass_naturality hS ⟨β, f, j, hβf, (cokernel.π_desc ..).symm⟩
  have h_nat₂ : c₂.extClass.comp (Ext.mk₀ u) (add_zero 1) =
      (Ext.mk₀ (β ≫ n)).comp hT.extClass (zero_add 1) :=
    c₂.extClass_naturality hT ⟨u, τ, β ≫ n, hu, hτ⟩
  -- The product with `ω` is bijective because `σ` is an equivalence for `F`.
  have h_bij {E : Type 1} [Category.{0} E] (Φ : AbFunctor C ⥤ AbFunctor E) [IsExactFunctor Φ]
      {F : AbFunctor E} (h_acyclic : ∀ k : ℕ, Subsingleton (H (Φ (cokernel i)) F k)) :
      Bijective (comp (F := F) (TotalH.map Φ ω)) := by
    have hσ : Bijective (pullbackAlong (G := F) (Φ.map (cokernel.π (kernel.ι σ)) ≫ Φ.map ι)) := by
      rw [← Φ.map_comp, Abelian.coimage.fac]
      exact (isCohomEquiv_pushout_desc h_comm Φ h_acyclic).bijective_pullbackAlong
    have hσ_comp : Bijective ((pullbackAlong (G := F) (Φ.map (cokernel.π (kernel.ι σ)))).comp
        (pullbackAlong (Φ.map ι))) := by
      simpa only [AddMonoidHom.coe_comp, Function.comp_def, pullbackAlong_pullbackAlong] using hσ
    -- The connecting maps of the two image sequences compose to a bijection.
    have h_tri := bijective_of_two_triangles (exact_triangle (c₁.map_of_exact Φ) F)
      (exact_triangle (c₂.map_of_exact Φ) F) hσ_comp
    -- `using!`: the image of an extension class under `Φ` is the class of the image sequence only
    -- up to unfolding `ShortComplex.map` (`Ext.mapExactFunctor_extClass`).
    simpa [ω, funext (map_comp_assoc _), Ext.mapExactFunctor_extClass] using! h_tri
  have h_class : comp ω (homClass u) =
      comp (homClass j) (hS.extClass.comp (H.map T.X₁ n 1 hT.extClass) rfl).toTotalH := by
    simp [ω, j, H.map, h_nat₂, ← Ext.comp_assoc (h₁₂ := zero_add 1), comp_of, ← h_nat₁]
  refine ⟨_, _, j, y, ω, ⟨?_, ?_, ?_⟩⟩
  · -- `e` kills the image of `σ`, so it factors through the cokernel.
    intro Q R e r s hi hδ hr
    have h_ι_e : ι ≫ e = 0 := by
      refine coequalizer.hom_ext ?_
      ext1 <;> simp [ι, σ, hi, hδ]
    exact ⟨cokernel.desc ι e h_ι_e, coequalizer.hom_ext (by simp [j, hr])⟩
  · -- Cancel `ω` in `j^* (η m) = ω s` to get `s = u^* m`, then `ε = y ≫ u`.
    intro E _ Φ _ F h_acyclic m s hs
    have h_nat : comp (TotalH.map Φ ω) (homClass (Φ.map u)) = pullbackAlong (Φ.map j)
        (TotalH.map Φ (hS.extClass.comp (H.map T.X₁ n 1 hT.extClass) rfl).toTotalH) := by
      simpa only [TotalH.map_comp, map_homClass] using congr(TotalH.map Φ $h_class)
    have hs_eq : pullbackAlong (Φ.map u) m = s :=
      (h_bij Φ h_acyclic).1 ((comp_assoc_of_sq h_nat m).trans hs)
    rw [← hs_eq, pullbackAlong_pullbackAlong, ← Φ.map_comp, hyu]
  · exact fun Φ _ _ h_acyclic ↦ (h_bij Φ h_acyclic).2

section

variable {p : ℕ} [ThePrime p]

open Period in
lemma gluing_apply_point (c : PadicTest)
    (t : (PadicTest.tilt ⋙ reprBy (CommAlgCat.of OFlat OFlat)).obj c) :
    (gluing.app c).hom (.of (⟨⟨false⟩, t⟩ : (tiltPointsSum pointOrTorus).obj c)) =
      .of (⟨⟨false⟩, ⟨evalZero _ ≫ t.down⟩⟩ : twoDiscs.obj c) := freeAb.desc_of ..

open Period in
lemma gluing_apply_torus (c : PadicTest) (t : (PadicTest.tilt ⋙ reprBy (monoidAlg ℚ)).obj c) :
    (gluing.app c).hom (.of (⟨⟨true⟩, t⟩ : (tiltPointsSum pointOrTorus).obj c)) =
      .of (⟨⟨false⟩, ⟨discToTorus (-NNRat.coeHom) ≫ t.down⟩⟩ : twoDiscs.obj c) -
        .of (⟨⟨true⟩, ⟨discToTorus NNRat.coeHom ≫ t.down⟩⟩ : twoDiscs.obj c) := freeAb.desc_of ..

end

variable {ℓ : ℕ}
  {A : Type} [CommRing A] [InvertsPrime A ℓ]
  {g : C ⥤ TestOver A} (M : TorsionCoeff g) (Θ : Theory g)
  {S : AbFunctor C} [HasFlatValues S]

-- Keeps definitional checks from unfolding the Ext groups and their group structure.
seal CategoryTheory.Abelian.Ext addCommGroupH in
/-- Let `S` have flat values, let `M` be a torsion coefficient and let `v` lie in total Ext(S, M).
Take the product `v η` in total Ext(S ⊗ ℤ[ℙ¹], M), with η = `etaClass g`, and move it by
`sliceEquiv` to the category of points (c, x) of ℙ¹. The result is the restriction of `v` there
composed with `cupClass`, the product with η at the tautological point x. -/
lemma TorsionCoeff.sliceEquiv_mulClass (v : TotalH S M.functor) :
    sliceEquiv (M.mulClass (etaClass g).toTotalH v) =
      comp (TotalH.map (restrictAlong (elementsProj (projLineAlong g))) v) M.cupClass.toTotalH := by
  let π : (projLineAlong g).Elements ⥤ C := elementsProj (projLineAlong g)
  let η : TotalH (freeAb (projLineAlong (π ⋙ g))) (tateModule (π ⋙ g)) :=
    (etaClass (π ⋙ g)).toTotalH
  -- Restricting along `π` and composing with the identity class is restricting along `π`.
  have h_id {N : AbFunctor C} (x : TotalH N M.functor) :
      mapThenComp (restrictAlong π) (homClass (𝟙 (π ⋙ M.functor))) x = TotalH.map (restrictAlong π)
        x :=
    comp_id
  -- Restriction to the points of the line commutes with the product by η, and η restricts to η.
  have h_res : TotalH.map (restrictAlong π) (M.mulClass (etaClass g).toTotalH v) =
      M.onElements.mulClass (S := π ⋙ S) η (TotalH.map (restrictAlong π) v) := by
    have h_natural := M.mulClass_naturality π M.onElements (homClass (𝟙 (π ⋙ M.functor)))
      (etaClass g).toTotalH v
    refine (h_id _).symm.trans (.trans ?_
      (congrArg (M.onElements.mulClass (S := π ⋙ S) η) (h_id v)))
    simp only [map_restrictAlong_etaClass] at h_natural
    exact h_natural
  -- Restricting and then evaluating at the tautological point is the definition of `sliceEquiv`.
  change pullbackAlong (tensorPoint (freeAb.map tautologicalSection) (π ⋙ S))
    (TotalH.map (restrictAlong π) (M.mulClass (etaClass g).toTotalH v)) = _
  refine (congrArg (pullbackAlong (tensorPoint (freeAb.map tautologicalSection) (π ⋙ S))) h_res).trans ?_
  exact M.onElements.mulClass_eq_comp_etaAt (S := π ⋙ S) η _ rfl _


/-- Let `Θ` be a theory along `g` with coefficient `F` (an `ℓ`-torsion coefficient with Zariski
descent that behaves well on closed loci), `S` a functor with flat ℤ-module values, and `x` a class
in total `Ext(S ⊗ ℤ[ℙ¹], F)` whose pull-back along `s ↦ s ⊗ [(1 : 1)]` is zero. Then
`x(q) η(r) = x(r) η(q)` (Yoneda composites) for all sections `q`, `r` of the line. Here `x(q)` is
the pull-back of `x` along `s ↦ s ⊗ [q]`, and `η(r) = Θ.etaAt r ∈ Ext²(F, F)` is the composite
`F → F ⊗ ℤ[ℙ¹] → (F ⊗ T)[2] → F[2]` of `y ↦ y ⊗ [r]`, of `F ⊗ η` and of the action of the Tate
module `T`. -/
lemma etaAt_swap (x : TotalH (abTensor S (freeAb (projLineAlong g))) Θ.functor)
    (h_inf : pullbackAlong (tensorPoint (freeAbSectionMap (basePt g)) S) x = 0)
    (q r : (projLineAlong g).sections) :
    comp (pullbackAlong (tensorPoint (freeAbSectionMap q) S) x)
        (Θ.etaAt (freeAbSectionMap r)).toTotalH =
      comp (pullbackAlong (tensorPoint (freeAbSectionMap r) S) x)
        (Θ.etaAt (freeAbSectionMap q)).toTotalH := by
  -- `t q` is evaluation at `q`, and `o q r` is the product `x(q) η(r)`.
  let t (q : (projLineAlong g).sections) : S ⟶ abTensor S (freeAb (projLineAlong g)) :=
    tensorPoint (freeAbSectionMap q) S
  let o (q r : (projLineAlong g).sections) : TotalH S Θ.functor :=
    comp (pullbackAlong (t q) x) (Θ.etaAt (freeAbSectionMap r)).toTotalH
  -- `η_q + η_r` comes from a class `ξ` relative to the locus where `J` is the unit ideal, and
  -- `q = r` where `J = 0`: the product with it does not see the difference of `t q` and `t r`.
  have h_sum (q r : (projLineAlong g).sections) : o q q + o q r = o r q + o r r := by
    obtain ⟨J, hJ, ξ, hξ⟩ := exists_etaClass_supported_diagonal q r
    have h_cut (a : (projLineAlong g).sections) (ha : ∀ c : C, J.ideal c = ⊥ → t a c = t r c) :
        o a q + o a r = pullbackAlong (tensorPoint (relFreeAb.π J.topLocus) S)
          (pullbackAlong ((abTensor.map (t r)).app _) (Θ.mulClass (.of _ 2 ξ) x)) := by
      rw [← Θ.mulClass_congr_of_eq_on_zeros J ξ ha x, Θ.mulClass_eq_comp_etaAt _ _ hξ]
      simp [o]
    rw [h_cut r fun _ _ ↦ rfl]
    refine h_cut q fun c hc ↦ ?_
    ext s
    change _ ⊗ₜ FreeAddCommGroup.of (q.val c) = _ ⊗ₜ FreeAddCommGroup.of (r.val c)
    rw [hJ c hc]
  -- Taking `r` to be the base point, where both `x` and `η` vanish, kills the diagonal terms.
  have h_diag (q : (projLineAlong g).sections) : o q q = 0 := by
    have h_eta_base : o q (basePt g) = 0 := Θ.comp_etaAt_basePt _
    have h_x_base (r : (projLineAlong g).sections) : o (basePt g) r = 0 := by
      simp [o, show pullbackAlong (t (basePt g)) x = 0 from h_inf]
    simpa [h_eta_base, h_x_base] using h_sum q (basePt g)
  simpa [h_diag] using h_sum q r

-- Keeps definitional checks from unfolding the group structure of the Ext groups.
seal addCommGroupH in
/-- For a theory `Θ` along `g` and `S` with flat values, the projective line formula
(`New.Variety.IsLerayHirschBasis` of `Θ.lineBasis`, the two classes η and 1 indexed by `Bool`) holds
at `S` under two conditions. First, `h_inj`: the product y ↦ y · η is injective, where `η`
(`etaClass g`) is the class in Ext²(ℤ[ℙ¹], 𝕋) with 𝕋 the Tate module, and the map goes from total
Ext(S, F) to total Ext(S ⊗ ℤ[ℙ¹], F). Second, `h_image`: its image contains every `x` on
`S ⊗ ℤ[ℙ¹]` whose slice `sliceEquiv x` times `η`, on the category of points of the line, equals the
restriction of `x` composed with `η` at the tautological point (`Θ.cupClass`). -/
lemma isLerayHirschBasis_lineBasis_of_injective
    (h_inj : Injective (Θ.mulClass (S := S) (etaClass g).toTotalH))
    (h_image : ∀ x : TotalH (abTensor S (freeAb (projLineAlong g))) Θ.functor,
      Θ.onElements.mulClass (S := elementsProj (projLineAlong g) ⋙ S)
          (etaClass (elementsProj (projLineAlong g) ⋙ g)).toTotalH (sliceEquiv x) =
        comp (TotalH.map (restrictAlong (elementsProj (projLineAlong g))) x) Θ.cupClass.toTotalH →
      x ∈ (Θ.mulClass (etaClass g).toTotalH).range) :
    IsLerayHirschBasis Θ.lineBasis S := by
  -- The product with `η` and evaluation `at_inf` at the base point form a short exact sequence.
  -- It is split by `pull`, the pull-back to the points of the line read through `sliceEquiv`,
  -- and its splitting is the Leray–Hirsch map.
  let at_inf : TotalH (abTensor S (freeAb (projLineAlong g))) Θ.functor →+ TotalH S Θ.functor :=
    pullbackAlong (tensorPoint (freeAbSectionMap (basePt g)) S)
  let pull : TotalH S Θ.functor →+ TotalH (abTensor S (freeAb (projLineAlong g))) Θ.functor :=
    sliceEquiv.symm.toAddMonoidHom.comp
      (TotalH.map (restrictAlong (elementsProj (projLineAlong g))))
  have h_exact : Exact (Θ.mulClass (S := S) (etaClass g).toTotalH).toIntLinearMap
      at_inf.toIntLinearMap := by
    -- One inclusion holds as `η` vanishes at the base point.
    have h_comp (v : TotalH S Θ.functor) : at_inf (Θ.mulClass (etaClass g).toTotalH v) = 0 :=
      (Θ.mulClass_eq_comp_etaAt _ _ rfl v).trans (Θ.comp_etaAt_basePt v)
    refine .of_comp_of_mem_range (funext h_comp) fun x h_inf ↦ h_image x (sliceEquiv.injective ?_)
    -- If `x` vanishes at the base point, `etaAt_swap` over pairs of points of the line exchanges
    -- the two tautological points `a`, `b`; this is the criterion `h_image`.
    let π₁ : (projLineAlong g).Elements ⥤ C := elementsProj (projLineAlong g)
    let π₂ : (projLineAlong (π₁ ⋙ g)).Elements ⥤ (projLineAlong g).Elements :=
      elementsProj (projLineAlong (π₁ ⋙ g))
    let a : (projLineAlong (π₂ ⋙ π₁ ⋙ g)).sections :=
      ⟨fun X ↦ (π₂.obj X).val, fun f ↦ (π₂.map f).map_val⟩
    let b : (projLineAlong (π₂ ⋙ π₁ ⋙ g)).sections := ⟨fun X ↦ X.val, fun f ↦ f.map_val⟩
    let x' : TotalH (abTensor (π₂ ⋙ π₁ ⋙ S) (freeAb (projLineAlong (π₂ ⋙ π₁ ⋙ g))))
        Θ.onElements.onElements.functor :=
      TotalH.map (restrictAlong π₂) (TotalH.map (restrictAlong π₁) x)
    -- Evaluation at the base point commutes with the two restrictions, and it kills `x`.
    have h_inf' : pullbackAlong
        (tensorPoint (freeAbSectionMap (basePt (π₂ ⋙ π₁ ⋙ g))) (π₂ ⋙ π₁ ⋙ S)) x' = 0 := by
      have h_restrict :
          TotalH.map (restrictAlong π₂) (TotalH.map (restrictAlong π₁) (at_inf x)) = 0 := by
        rw [show at_inf x = 0 from h_inf, map_zero, map_zero]
      -- `using!`: the restricted base point and evaluation there agree with those of the
      -- restricted line only up to unfolding definitions.
      simpa -dsimp [at_inf, map_pullbackAlong] using! h_restrict
    -- Restriction respects products, and it takes `η` at a point to `η` at that point.
    have h_cup : TotalH.map (restrictAlong π₂)
          (comp (TotalH.map (restrictAlong π₁) x) Θ.cupClass.toTotalH) =
        comp x' (Θ.onElements.onElements.etaAt (freeAbSectionMap a)).toTotalH :=
      (map_comp _).trans (congrArg (comp x') (Θ.onElements.map_etaAt_onElements _ _))
    refine (Θ.onElements.sliceEquiv_mulClass (S := π₁ ⋙ S) (sliceEquiv x)).trans ?_
    have h_first :
        comp (TotalH.map (restrictAlong π₂) (sliceEquiv x)) Θ.onElements.cupClass.toTotalH =
          comp (pullbackAlong (tensorPoint (freeAbSectionMap a) (π₂ ⋙ π₁ ⋙ S)) x')
            (Θ.onElements.onElements.etaAt (freeAbSectionMap b)).toTotalH :=
      congrArg (fun ξ ↦ comp ξ Θ.onElements.cupClass.toTotalH) map_pullbackAlong
    exact h_first.trans ((etaAt_swap Θ.onElements.onElements x' h_inf' a b).trans
      ((comp_assoc ..).trans (congrArg (pullbackAlong _) h_cup.symm)))

  -- Restriction `r` from the points of the line to the base point undoes the pull-back, and it
  -- corresponds to `at_inf` under `sliceEquiv`.
  let r {N : AbFunctor C} : TotalH (elementsProj (projLineAlong g) ⋙ N)
      (elementsProj (projLineAlong g) ⋙ Θ.functor) →+ TotalH N Θ.functor :=
    TotalH.map (restrictAlong (sectionLift (𝟭 C) (basePt g)))
  have h_res {N : AbFunctor C} (x : TotalH N Θ.functor) :
      r (TotalH.map (restrictAlong (elementsProj (projLineAlong g))) x) = x :=
    (x.map_map (restrictAlong (elementsProj (projLineAlong g)))
      (restrictAlong (sectionLift (𝟭 C) (basePt g)))).trans x.map_id
  have h_base (x : TotalH (abTensor S (freeAb (projLineAlong g))) Θ.functor) :
      r (sliceEquiv x) = at_inf x := map_pullbackAlong.trans (congrArg _ (h_res x))
  have h_section (x : TotalH S Θ.functor) : at_inf (pull x) = x := by
    rw [← h_base]
    exact (congrArg r (sliceEquiv.apply_symm_apply _)).trans (h_res x)
  let split : (TotalH S Θ.functor × TotalH S Θ.functor) ≃ₗ[ℤ]
      TotalH (abTensor S (freeAb (projLineAlong g))) Θ.functor :=
    (Exact.splitSurjectiveEquiv h_exact h_inj
      ⟨pull.toIntLinearMap, LinearMap.ext h_section⟩).val.symm
  -- A family indexed by `Bool` is a pair: first the coefficient of `η`, then that of `1`.
  let pair : (Bool →₀ TotalH S Θ.functor) ≃ TotalH S Θ.functor × TotalH S Θ.functor :=
    equivFunOnFinite.trans (.boolArrowEquivProd _)
  refine (Comparison.bijective_iff_of_comm_sq (fun p ↦ ?_) pair.symm.bijective
    sliceEquiv.bijective).1 split.bijective
  -- Both sides are the sum of `π^* p.2` and `π^* p.1 · η`, with `π^*` the restriction to the points
  -- of the line, in opposite orders.
  simp [split, pair, pull, lerayHirsch, sum_fintype, mapThenComp, TorsionCoeff.lineBasis,
    Exact.splitSurjectiveEquiv]
  let π := elementsProj (projLineAlong g)
  change _ = sliceEquiv
    (Θ.mulClass (etaClass g).toTotalH p.1 + sliceEquiv.symm (TotalH.map (restrictAlong π) p.2))
  refine (add_comm _ _).trans ?_
  exact ((map_add sliceEquiv _ _).trans
    (congrArg₂ (· + ·) (Θ.sliceEquiv_mulClass ..) (sliceEquiv.apply_symm_apply _))).symm


-- Keeps definitional checks from unfolding the group structure of the Ext groups.
seal addCommGroupH in
open TensorProduct in
/-- The projective line formula holds for a theory `Θ` along `g` if the class `η` is cancelled
(`New.Variety.IsTodaCancellation`) along a map `i`, with `ε` the generator `tateGen` of the Tate
module, and `S ⊗ coker i` is acyclic for the coefficient of `Θ` whenever `S` has flat values. -/
lemma hasLineFormula_of_isTodaCancellation {B K : AbFunctor C} {i : W' ⟶ W} {δ : W ⟶ W}
    {q : W ⟶ freeAb (projLineAlong g)} {j : B ⟶ freeAb (projLineAlong g)}
    {y : freeAb (onePointFunctor C) ⟶ K} {ω : TotalH B K}
    (h_toda : IsTodaCancellation i δ q (etaClass g) (tateGen g) j y ω)
    (h_acyclic : ∀ (S : AbFunctor C) [HasFlatValues S] (n : ℕ),
      Subsingleton (H (abTensor S (cokernel i)) Θ.functor n)) :
    Θ.HasLineFormula := by
  -- Check the two conditions of `isLerayHirschBasis_lineBasis_of_injective`.
  -- It suffices to treat representable `S = ℤ[h_c]`.
  refine isLerayHirschBasis_of_reprBy fun c ↦
    isLerayHirschBasis_lineBasis_of_injective Θ ((injective_iff_map_eq_zero _).2 fun v hv ↦ ?_)
      fun x hx ↦ ?_
  · -- If `η v = 0`, take `s = 0` in `h_toda`: the action `m` of the Tate module on `v` pulls
    -- back to `0` along the generator `tateGen`, and that pull-back is `v`.
    let Φ : AbFunctor C ⥤ AbFunctor C := abTensor (freeAb (reprBy c))
    let m : TotalH (Φ (tateModule g)) Θ.functor :=
      comp (TotalH.map (abTensor.flip _) v) Θ.tateAction.toTotalH
    have h_eq : pullbackAlong (Φ.map j) (comp (TotalH.map Φ (etaClass g).toTotalH) m) =
        comp (TotalH.map Φ ω) 0 := by
      rw [show comp (TotalH.map Φ (etaClass _).toTotalH) m = 0 from hv, map_zero, map_zero]
    have h_pull : pullbackAlong (tensorPoint (tateGen _) _) m = 0 :=
      (h_toda.pullbackAlong_comp_map_eq Φ (h_acyclic _) (tensorPoint (𝟙 _) _) m 0 h_eq).trans
        (map_zero _)
    exact (Θ.pullbackAlong_tensorPoint_comp_tateAction v).symm.trans h_pull
  -- Write `j^* x = ω w`; the preimage of `x` is `y^* w`. Check this over the points of `ℙ¹`.
  let S : AbFunctor C := freeAb (reprBy c)
  let L : AbFunctor C := freeAb (projLineAlong g)
  obtain ⟨w, hw⟩ : ∃ w : TotalH (abTensor S K) Θ.functor,
      comp (TotalH.map (abTensor S) ω) w = pullbackAlong ((abTensor S).map j) x :=
    h_toda.surjective (abTensor S) (h_acyclic S) _
  refine ⟨pullbackAlong (tensorPoint y _) w, sliceEquiv.injective ?_⟩
  -- Over the points of `ℙ¹`, apply `h_toda` to the functor `Φ`, with `m` the action of the Tate
  -- module on `x` and `s = w η`.
  let π : (projLineAlong g).Elements ⥤ C := elementsProj (projLineAlong g)
  let Φ : AbFunctor C ⥤ AbFunctor (projLineAlong g).Elements := restrictAlong π ⋙ abTensor (π ⋙ S)
  let m : TotalH (Φ (tateModule g)) Θ.onElements.functor :=
    comp (TotalH.map (abTensor.flip (tateModule (π ⋙ g))) (sliceEquiv x))
      Θ.onElements.tateAction.toTotalH
  let s : TotalH (Φ K) Θ.onElements.functor :=
    comp (TotalH.map (restrictAlong π) w) Θ.cupClass.toTotalH
  -- The hypothesis `j^* (η m) = ω s` of `h_toda` follows from `hx` and `hw`.
  have h_eq : pullbackAlong (Φ.map j) (comp (TotalH.map Φ (etaClass g).toTotalH) m) =
      comp (TotalH.map Φ ω) s := by
    have h_eta : comp (TotalH.map Φ (etaClass g).toTotalH) m =
        comp (TotalH.map (restrictAlong π) x) Θ.cupClass.toTotalH := by
      -- `erw`: the left side is the product by `η` of `hx` only up to unfolding `Φ` and `m`.
      erw [← TotalH.map_map, map_restrictAlong_etaClass, hx]
    have h_restrict :
        comp (TotalH.map (restrictAlong π) (pullbackAlong ((abTensor S).map j) x))
          Θ.cupClass.toTotalH =
        comp (TotalH.map (restrictAlong π) (comp (TotalH.map (abTensor S) ω) w))
          Θ.cupClass.toTotalH := by rw [hw]
    rw [h_eta]
    -- `using!`: restriction along the points of `ℙ¹` matches `Φ` only up to unfolding.
    erw [map_pullbackAlong, comp_assoc, map_comp_assoc, TotalH.map_map] at h_restrict
    exact h_restrict
  -- Acyclicity over the points of `ℙ¹` is that of `h_c × ℙ¹`, after swapping two tensor factors.
  have h_acyclic_Φ (n : ℕ) : Subsingleton (H (Φ (cokernel i)) Θ.onElements.functor n) := by
    let swap : abTensor (abTensor S L) (cokernel i) ≅
        abTensor (abTensor S (cokernel i)) L :=
      NatIso.ofComponents (fun _ ↦ (rightComm ℤ _ _ _).toAddCommGrpIso) fun _ ↦ by
        refine addCommGrp_tensor_hom_ext fun t ↦ ?_
        induction t using TensorProduct.inductionOn with
        | tmul x l => exact fun r ↦ rfl
        | add x x' h₁ h₂ =>
          intro r
          erw [add_tmul, _root_.map_add, _root_.map_add, h₁ r, h₂ r]
    have h_line (k : ℕ) : Subsingleton (H (abTensor (abTensor S L) (cokernel i)) Θ.functor k) :=
      h_acyclic (abTensor S L) k
    have h_swapped : Subsingleton (TotalH (abTensor (abTensor S (cokernel i)) L) Θ.functor) :=
      (IsCohomEquiv.of_isIso swap.hom).bijective_pullbackAlong.injective.subsingleton
    have h_total : Subsingleton (TotalH (Φ (cokernel i)) Θ.onElements.functor) :=
      (sliceEquiv (N := abTensor S (cokernel i))).symm.injective.subsingleton
    exact (DirectSum.of_injective (β := H (Φ (cokernel i)) Θ.onElements.functor) n).subsingleton
  have h_first :
      sliceEquiv (Θ.mulClass (S := S) (etaClass g).toTotalH (pullbackAlong (tensorPoint y S) w)) =
        pullbackAlong (tensorPoint (𝟙 _) (π ⋙ S) ≫ Φ.map y) s := by
    erw [Θ.sliceEquiv_mulClass, map_pullbackAlong, comp_assoc]
    rfl
  exact h_first.trans ((h_toda.pullbackAlong_comp_map_eq Φ h_acyclic_Φ _ m s h_eq).symm.trans
    (Θ.onElements.pullbackAlong_tensorPoint_comp_tateAction (S := π ⋙ S) _))

open Period in
/-- The roots of unity `compatibleRootsOfUnity` of `A`, mapped to `ℂ_ℓ`, lift to a character `χ` of
`ℚ` with values in `O^♭`: the untilt of `χ s` is the image of the root of unity at `s`. -/
private lemma exists_tilt_lift_compatibleRootsOfUnity [Algebra A ℂ_[ℓ]] :
    ∃ χ : Multiplicative ℚ →* OFlat, ∀ s : Multiplicative ℚ,
      ((χ s).untilt : ℂ_[ℓ]) = algebraMap A ℂ_[ℓ]
        ((compatibleRootsOfUnity (ℓ := ℓ) (A := A)).val s : A) := by
  have h_root : (compatibleRootsOfUnity (ℓ := ℓ) (A := A)).val (.ofAdd 1) = 1 :=
    (compatibleRootsOfUnity (ℓ := ℓ) (A := A)).property.left
  let a : Multiplicative ℚ →* ℂ_[ℓ] :=
    (algebraMap A ℂ_[ℓ]).toMonoidHom.comp
      ((Units.coeHom A).comp (compatibleRootsOfUnity (ℓ := ℓ)).val)
  exact exists_tilt_lift_of_character a (by simp [a, h_root])

open AddMonoidAlgebra Period freeAb in
/-- On the cover of the perfect projective line by two discs glued along the torus, let `χ` be a
character of `ℚ` with values in `O^♭`, whose operators `1 - Δ` (`oneSub`, with Δ the twist
`charTwist χ`: `discTwist χ` on the discs, `pointOrTorusTwist χ` on the source of the gluing)
commute with the gluing map (`oneSub_comp_gluing`). Let `f`, `α`, `κ` satisfy the three conditions
of `exists_isTodaCancellation` for this square (`h_torus`, `h_disc`, `h_kummer`), with `κ` at the
origin equal to `tateGen`. Then the class `η` is cancelled, with `ε` the generator `tateGen`. -/
private lemma exists_isTodaCancellation_etaClass_of_squares [Algebra A ℂ_[ℓ]]
    (χ : Multiplicative ℚ →* OFlat)
    (f : freeAb twoDiscs ⟶ (cocycle (genericTestOver A)).extension.X₂)
    (α : freeAb (tiltPointsSum pointOrTorus) ⟶ (kummerSeq (genericTestOver A)).X₂)
    (κ : freeAb twoDiscs ⟶ (kummerSeq (genericTestOver A)).X₁)
    (h_torus : (α ≫ (kummerSeq (genericTestOver A)).g) ≫
      (cocycle (genericTestOver A)).extension.f = gluing ≫ f)
    (h_disc : oneSub (discTwist χ) ≫ f = 0)
    (h_kummer : oneSub (pointOrTorusTwist χ) ≫ α = gluing ≫ κ ≫ (kummerSeq (genericTestOver A)).f)
    (h_gen : origin ⟨true⟩ ≫ κ = tateGen (genericTestOver A)) :
    ∃ (δ : freeAb twoDiscs ⟶ freeAb twoDiscs)
      (q : freeAb twoDiscs ⟶ freeAb (projLineAlong (genericTestOver A)))
      (B K : AbFunctor PadicTest) (j : B ⟶ freeAb (projLineAlong (genericTestOver A)))
      (y : freeAb (onePointFunctor PadicTest) ⟶ K) (ω : TotalH B K),
      IsTodaCancellation gluing δ q (etaClass (genericTestOver A)) (tateGen (genericTestOver A))
        j y ω := by
  -- The twist of either disc fixes the origin.
  have h_origin : origin ⟨true⟩ ≫ oneSub (discTwist χ) = 0 := by
    refine freeAb.hom_ext fun c x ↦ ?_
    let z : twoDiscs.obj c := ⟨⟨true⟩, ⟨evalZero _⟩⟩
    have h_origin_app : (origin ⟨true⟩).app c (FreeAddCommGroup.of x) = FreeAddCommGroup.of z :=
      freeAb.desc_of ..
    let z' : twoDiscs.obj c :=
      ⟨⟨true⟩, ⟨discTwist χ ⟨true⟩ ≫ evalZero (PadicTest.tilt.obj c)⟩⟩
    have h_twist : (oneSub (discTwist χ)).app c (.of z) = .of z - .of z' :=
      freeAb.desc_of ..
    have h_fixed : z' = z :=
      congrArg (fun t ↦ (⟨⟨true⟩, ⟨t⟩⟩ : twoDiscs.obj c)) (discTwist_comp_evalZero ..)
    exact (congrArg ((oneSub (discTwist χ)).app c) h_origin_app).trans
      (h_twist.trans (sub_eq_zero.mpr (congrArg FreeAddCommGroup.of h_fixed.symm)))
  obtain ⟨B, K, j, y, ω, h_toda⟩ := exists_isTodaCancellation (oneSub_comp_gluing χ) (origin ⟨true⟩)
    h_origin
    (cocycle _).shortExact_extension (shortExact_kummerSeq (genericTestOver A)) f α κ (𝟙 _) _
    h_torus h_disc h_kummer (Category.comp_id _)
  -- The 2-extension along the identity is `η`.
  have h_eta : (cocycle (genericTestOver A)).shortExact_extension.extClass.comp
      (H.map _ (𝟙 _) 1 (shortExact_kummerSeq (genericTestOver A)).extClass) rfl =
      etaClass (genericTestOver A) := by
    unfold etaClass
    exact congrArg (fun x ↦ (cocycle (genericTestOver A)).shortExact_extension.extClass.comp x rfl)
      (H.map_id (x := (shortExact_kummerSeq (genericTestOver A)).extClass))
  refine ⟨oneSub (discTwist χ), f ≫ (cocycle (genericTestOver A)).extension.g, B, K, j, y, ω, ?_⟩
  rw [← h_eta, ← h_gen]
  exact h_toda

open AddMonoidAlgebra Period freeAb in
/-- On the cover of the perfect projective line by two discs glued along the torus (`gluing`), the
class `η` is cancelled, with `ε` the generator `tateGen` of the Tate module. That is, some `δ`, `q`,
`j`, `y`, `ω` satisfy `IsTodaCancellation`. So after any exact functor making `coker gluing`
acyclic, product with `ω` is onto and `j^*(η m)` determines `ε^* m`. -/
lemma exists_isTodaCancellation_etaClass [Algebra A ℂ_[ℓ]] :
    ∃ (δ : freeAb twoDiscs ⟶ freeAb twoDiscs)
      (q : freeAb twoDiscs ⟶ freeAb (projLineAlong (genericTestOver A)))
      (B K : AbFunctor PadicTest) (j : B ⟶ freeAb (projLineAlong (genericTestOver A)))
      (y : freeAb (onePointFunctor PadicTest) ⟶ K) (ω : TotalH B K),
      IsTodaCancellation gluing δ q (etaClass (genericTestOver A)) (tateGen (genericTestOver A))
        j y ω := by
  -- The gluing map commutes with the operators `1 - charTwist χ _` (`oneSub_comp_gluing`); read `η`
  -- on this square by `exists_isTodaCancellation_etaClass_of_squares`. First, the character `χ` of
  -- `ℚ` with values in the tilt that lifts the roots of unity `compatibleRootsOfUnity`, which are
  -- `1` at `1`.
  have h_root : (compatibleRootsOfUnity (ℓ := ℓ) (A := A)).val (.ofAdd 1) = 1 :=
    (compatibleRootsOfUnity (ℓ := ℓ) (A := A)).property.left
  obtain ⟨χ, hχ⟩ := exists_tilt_lift_compatibleRootsOfUnity (A := A)
  -- The row `(1 + x.1 * x.2, x.2)` is the unit `ε x` times the chosen row of its class. `F c x` is
  -- this frame, a unit and a point of `ℙ¹`; it is natural in `c`.
  let R : PadicTest ⥤ CommRingCat := ringOf (genericTestOver A)
  have h_row : ∀ (B : CommRingCat) (x : B × B),
      ∃ ε : Bˣ, (1 + x.1 * x.2, x.2) = ε.val • unimodularRow ⟨⟦x⟧⟩ :=
    fun _ x ↦ exists_unit_smul_unimodularRow x
  choose ε hε using h_row
  let F (c : PadicTest) (x : R c × R c) : (cocycle (genericTestOver A)).extension.X₂ c :=
    (⟨ε (R.obj c) x⟩, .of ⟨⟦x⟧⟩)
  have F_nat (c d : PadicTest) (f : c ⟶ d) (x : R c × R c) :
      (cocycle _).extension.X₂.map f (F c x) = F d (R.map f x.1, R.map f x.2) := by
    -- `R.map f` sends `ε x` times the row of `⟦x⟧`, that is `(1 + x.1 * x.2, x.2)`, to the row of
    -- the image pair.
    have h_image : Prod.map (R.map f) (R.map f) ((ε (R.obj c) x).val • unimodularRow ⟨⟦x⟧⟩) =
        (1 + R.map f x.1 * R.map f x.2, R.map f x.2) := by
      rw [← hε (R.obj c) x]
      simp only [Prod.map_apply, RingHom.map_add, RingHom.map_one, RingHom.map_mul]
    have h_row := hε (R.obj d) (R.map f x.1, R.map f x.2)
    exact Prod.ext (add_rowUnit_eq (R.map f) _ (h_image.trans h_row)) rfl
  -- The untilt `ρ` is natural, and it sends a constant `s` from `OFlat` to the untilt of `s`.
  let ρ (c : PadicTest) : PadicTest.tilt c →*₀ c.GenericRing :=
    .comp (.ofClass (algebraMap ..)) (Perfection.teichmuller₀ ..)
  have ρ_nat (c d : PadicTest) (f : c ⟶ d) (x : PadicTest.tilt c) :
      R.map f (ρ c x) = ρ d (tiltMap f.toRingHom x) := by
    -- These lemmas match `R.map f` and `ρ` only up to unfolding definitions.
    exact (c.mapGeneric_algebraMap _ _).trans (congrArg _ (untilt_tiltMap ..).symm)
  have ρ_const (c : PadicTest) (s : OFlat) :
      ρ c (algebraMap _ _ s) = c.genericStructureMap s.untilt := by
    -- As for `ρ_nat`, these lemmas match only up to unfolding definitions.
    exact ((c.genericStructureMap_coe _).trans (congrArg _ (untilt_tiltMap c.structureMap s).symm)).symm
  -- With `X` the untilt of the coordinate, `f` is `[(1, 0)] - [(X, 1)]` on the disc `true` and
  -- `[(1, 0)] - [(1, X)]` on the other one.
  let f : freeAb twoDiscs ⟶ (cocycle (genericTestOver A)).extension.X₂ := desc
    (fun c y ↦ F c (0, 0) -
      F c (cond y.fst.down (fun X ↦ (X - 1, 1)) (fun X ↦ (0, X))
        (ρ c (y.snd.down.hom (single 1 1)))))
    (by
      -- On each disc, `twoDiscs.map` keeps the disc and composes the point, by definition.
      rintro c d j ⟨⟨_ | _⟩, y⟩
      · let x := y.down.hom (single 1 1)
        change F d (0, 0) - F d (0, ρ d (tiltMap j.toRingHom x)) =
          ((cocycle _).extension.X₂.map j).hom (F c (0, 0) - F c (0, ρ c x))
        erw [_root_.map_sub, F_nat c d j (0, 0), F_nat c d j (0, ρ c x)]
        simp [ρ_nat]
      · let x := y.down.hom (single 1 1)
        let xc : R c := ρ c x
        let xd : R d := ρ d (tiltMap j.toRingHom x)
        change F d (0, 0) - F d (xd - 1, 1) =
          ((cocycle _).extension.X₂.map j).hom (F c (0, 0) - F c (xc - 1, 1))
        erw [_root_.map_sub, F_nat c d j (0, 0), F_nat c d j (xc - 1, 1)]
        simp [xc, xd]
        erw [map_sub, map_one, ρ_nat]
        rfl)

  -- `α` sends a point `t` of the torus to `pow c t`, the untilts of the powers of the coordinate.
  let pow (c : PadicTest) (t : (PadicTest.tilt ⋙ reprBy (monoidAlg ℚ)).obj c) :
      (kummerSeq (genericTestOver A)).X₂ c :=
    .comp (.mk' ULift.up fun _ _ ↦ rfl)
      ((ρ c).toMonoidHom.comp
        (t.down.hom.toRingHom.toMonoidHom.comp (of OFlat ℚ))).toHomUnits.toAdditiveRight
  let α : freeAb (tiltPointsSum pointOrTorus) ⟶ (kummerSeq (genericTestOver A)).X₂ :=
    projFirst ≫ desc pow fun c d φ t ↦ AddMonoidHom.ext fun s ↦ Gm.ext.2 (ρ_nat c d φ _).symm
  let κ : freeAb twoDiscs ⟶ (kummerSeq (genericTestOver A)).X₁ :=
    projFirst ≫ freeAb.map (toUnit _) ≫ tateGen _
  -- The three squares that `exists_isTodaCancellation_etaClass_of_squares` needs, each checked on
  -- the generators of a free functor.
  have h_f_app (c : PadicTest) (y : twoDiscs.obj c) :
      (f.app c).hom (FreeAddCommGroup.of y) = F c (0, 0) -
        F c (cond y.fst.down (fun X ↦ (X - 1, 1)) (fun X ↦ (0, X))
          (ρ c (y.snd.down.hom (single 1 1)))) := freeAb.desc_of ..
  have h_alpha (c : PadicTest) (q : (PadicTest.tilt ⋙ reprBy (monoidAlg ℚ)).obj c) :
      (α.app c).hom (FreeAddCommGroup.of (⟨⟨true⟩, q⟩ : (tiltPointsSum pointOrTorus).obj c)) =
        pow c q := by
    let r : (tiltPointsSum pointOrTorus).obj c := ⟨⟨true⟩, q⟩
    change FreeAddCommGroup.lift (pow c)
      (((projFirst (B := pointOrTorus)).app c).hom (FreeAddCommGroup.of r)) = _
    erw [projFirst_true (B := pointOrTorus) c q, FreeAddCommGroup.lift_apply_of]
  have h_torus : (α ≫ (kummerSeq (genericTestOver A)).g) ≫
      (cocycle (genericTestOver A)).extension.f = gluing ≫ f := by
    -- On the torus the frames `(X, 1)` and `(1, X⁻¹)` differ by the unit `X`.
    refine hom_ext ?_
    rintro c ⟨⟨_ | _⟩, y⟩
    · let y₀ : (tiltPointsSum pointOrTorus).obj c := ⟨⟨false⟩, y⟩
      let z : twoDiscs.obj c := ⟨⟨false⟩, ⟨evalZero (PadicTest.tilt.obj c)⟩⟩
      have h_glue : (gluing.app c).hom (FreeAddCommGroup.of y₀) = FreeAddCommGroup.of z := by
        simpa only [y₀, z, evalZero_comp] using gluing_apply_point c y
      have h_a : (α.app c).hom (FreeAddCommGroup.of y₀) = 0 := by
        change FreeAddCommGroup.lift (pow c)
          (((projFirst (B := pointOrTorus)).app c).hom (FreeAddCommGroup.of y₀)) = 0
        erw [projFirst_false (B := pointOrTorus) c y, map_zero]
      change ((cocycle _).extension.f.app c).hom
          (((kummerSeq (genericTestOver A)).g.app c).hom ((α.app c).hom (FreeAddCommGroup.of y₀))) =
        (f.app c).hom ((gluing.app c).hom (FreeAddCommGroup.of y₀))
      erw [h_a, h_glue, h_f_app]
      simp [z, evalZero]
      erw [map_zero, sub_self]
    · let X : R c := ρ c (y.down.hom (single 1 1))
      let X' : R c := ρ c (y.down.hom (single (-1) 1))
      let v : (cocycle (genericTestOver A)).extension.X₂ c :=
        ((cocycle (genericTestOver A)).extension.f.app c).hom
          (((kummerSeq (genericTestOver A)).g.app c).hom (pow c y))
      -- The first component of `v` is the unit `X`, with inverse `X'`.
      have h_rows : (v + F c (0, X')).1.down.val • unimodularRow (B := R c) ⟨⟦(0, X')⟧⟩ =
          (F c (X - 1, 1)).1.down.val • unimodularRow (B := R c) ⟨⟦(X - 1, 1)⟧⟩ := by
        -- `erw`: the rows of the two frames match `hε` only up to unfolding definitions.
        erw [mul_smul, ← hε, ← hε]
        simpa only [zero_mul, add_zero, Prod.smul_mk, smul_eq_mul, mul_one, add_sub_cancel,
          Prod.mk.injEq] using ⟨rfl, Units.mul_inv _⟩
      obtain ⟨h_unit, h_point⟩ := eq_and_eq_of_smul_unimodularRow_eq h_rows
      have h_frame : v + F c (0, X') = F c (X - 1, 1) :=
        Prod.ext (ULift.down_injective h_unit)
          ((zero_add _).trans (congrArg FreeAddCommGroup.of h_point))
      let y₁ : (tiltPointsSum pointOrTorus).obj c := ⟨⟨true⟩, y⟩
      let z₀ : twoDiscs.obj c := ⟨⟨false⟩, ⟨discToTorus (-NNRat.coeHom) ≫ y.down⟩⟩
      let z₁ : twoDiscs.obj c := ⟨⟨true⟩, ⟨discToTorus NNRat.coeHom ≫ y.down⟩⟩
      have h_glue := gluing_apply_torus c y
      change ((cocycle _).extension.f.app c).hom
          (((kummerSeq (genericTestOver A)).g.app c).hom ((α.app c).hom (FreeAddCommGroup.of y₁))) =
        (f.app c).hom ((gluing.app c).hom (FreeAddCommGroup.of y₁))
      erw [h_alpha, h_glue, _root_.map_sub, h_f_app, h_f_app]
      have h_coord (g : ℚ≥0 →+ ℚ) :
          (discToTorus g ≫ y.down).hom (single 1 1) = y.down.hom (single (g 1) 1) := by
        change y.down.hom (mapDomain g (single 1 1)) = _
        exact congrArg y.down.hom (AddMonoidAlgebra.mapDomain_single ..)
      simp only [Bool.cond_false, Bool.cond_true, h_coord]
      change v = (F c (0, 0) - F c (0, X')) - (F c (0, 0) - F c (X - 1, 1))
      simpa only [sub_sub_sub_cancel_left, eq_sub_iff_add_eq] using h_frame

  have h_disc : oneSub (discTwist χ) ≫ f = 0 := by
    -- `charTwist χ` fixes `X`, as the roots of unity are trivial at `1` and `-1`.
    refine freeAb.hom_ext fun c y ↦ ?_
    let y' : twoDiscs.obj c := ⟨y.fst, ⟨discTwist χ y.fst ≫ y.snd.down⟩⟩
    erw [NatTrans.comp_app, AddCommGrpCat.comp_apply]
    change (f.app c).hom (FreeAddCommGroup.lift _ (FreeAddCommGroup.of y)) = _
    rw [FreeAddCommGroup.lift_apply_of]
    change (f.app c).hom (FreeAddCommGroup.of y - FreeAddCommGroup.of y') = 0
    erw [_root_.map_sub, h_f_app, h_f_app]
    rcases y with ⟨⟨_ | _⟩, y⟩ <;>
      simp [y', discTwist, charTwist, ρ_const, hχ, h_root, -coe_algebraMap, -Functor.comp_obj]
  have h_kummer : oneSub (pointOrTorusTwist χ) ≫ α =
      gluing ≫ κ ≫ (kummerSeq (genericTestOver A)).f := by
    -- `charTwist χ` multiplies the untilted powers by the roots of unity of `tateGen`.
    refine hom_ext ?_
    rintro c ⟨⟨_ | _⟩, y⟩
    · let y₀ : (tiltPointsSum pointOrTorus).obj c := ⟨⟨false⟩, y⟩
      let z : twoDiscs.obj c := ⟨⟨false⟩, ⟨evalZero (PadicTest.tilt.obj c)⟩⟩
      have h_twist : ((oneSub (pointOrTorusTwist χ)).app c).hom
          (FreeAddCommGroup.of y₀) = 0 := by
        change FreeAddCommGroup.lift _ (FreeAddCommGroup.of y₀) = _
        rw [FreeAddCommGroup.lift_apply_of]
        change Sub.sub (FreeAddCommGroup.of y₀)
          (FreeAddCommGroup.of (⟨⟨false⟩, ⟨𝟙 _ ≫ y.down⟩⟩ : (tiltPointsSum pointOrTorus).obj c)) = 0
        rw [Category.id_comp]
        exact sub_self _
      have h_glue : (gluing.app c).hom (FreeAddCommGroup.of y₀) = FreeAddCommGroup.of z := by
        simpa only [y₀, z, evalZero_comp] using gluing_apply_point c y
      change (α.app c).hom (((oneSub (pointOrTorusTwist χ)).app c).hom (FreeAddCommGroup.of y₀)) =
        ((kummerSeq (genericTestOver A)).f.app c).hom
          ((κ.app c).hom ((gluing.app c).hom (FreeAddCommGroup.of y₀)))
      rw [h_twist, h_glue]
      change _ = ((kummerSeq (genericTestOver A)).f.app c).hom
        (((tateGen (genericTestOver A)).app c).hom ((freeAb.map (toUnit _)).app c
          (((projFirst (B := fun _ ↦ monoidAlg ℚ≥0)).app c).hom (FreeAddCommGroup.of z))))
      rw [projFirst_false (B := fun _ ↦ monoidAlg ℚ≥0) c z.snd]
      simp only [map_zero]
    · let y₁ : (tiltPointsSum pointOrTorus).obj c := ⟨⟨true⟩, y⟩
      let t : (PadicTest.tilt ⋙ reprBy (monoidAlg ℚ)).obj c :=
        ⟨charTwist χ (AddMonoidHom.id ℚ) ≫ y.down⟩
      let z₀ : twoDiscs.obj c := ⟨⟨false⟩, ⟨discToTorus (-NNRat.coeHom) ≫ y.down⟩⟩
      let z₁ : twoDiscs.obj c := ⟨⟨true⟩, ⟨discToTorus NNRat.coeHom ≫ y.down⟩⟩
      have h_glue := gluing_apply_torus c y
      let π := (freeAb.map (toUnit (PadicTest.tilt ⋙ reprBy (monoidAlg ℚ≥0)))).app c
      let τ := ((tateGen (genericTestOver A)).app c).hom
      have h_zero : (κ.app c).hom (FreeAddCommGroup.of z₀) = 0 := by
        change τ (π (((projFirst (B := fun _ ↦ monoidAlg ℚ≥0)).app c).hom
          (FreeAddCommGroup.of z₀))) = 0
        rw [projFirst_false (B := fun _ ↦ monoidAlg ℚ≥0) c z₀.snd]
        simp only [map_zero]
      have h_one : (κ.app c).hom (FreeAddCommGroup.of z₁) = τ (FreeAddCommGroup.of PUnit.unit) := by
        change τ (π (((projFirst (B := fun _ ↦ monoidAlg ℚ≥0)).app c).hom
          (FreeAddCommGroup.of z₁))) = _
        rw [projFirst_true (B := fun _ ↦ monoidAlg ℚ≥0) c z₁.snd]
        change τ ((freeAb.map (toUnit (PadicTest.tilt ⋙ reprBy (monoidAlg ℚ≥0)))).app c
          (FreeAddCommGroup.of z₁.snd)) = _
        rw [freeAb.map_of]
        rfl
      change (α.app c).hom (((oneSub (pointOrTorusTwist χ)).app c).hom (FreeAddCommGroup.of y₁)) =
        ((kummerSeq (genericTestOver A)).f.app c).hom
          ((κ.app c).hom ((gluing.app c).hom (FreeAddCommGroup.of y₁)))
      change (α.app c).hom (FreeAddCommGroup.lift _ (FreeAddCommGroup.of y₁)) = _
      rw [FreeAddCommGroup.lift_apply_of]
      let t₁ : (tiltPointsSum pointOrTorus).obj c := ⟨⟨true⟩, t⟩
      change (α.app c).hom (FreeAddCommGroup.of y₁ - FreeAddCommGroup.of t₁) = _
      erw [_root_.map_sub, h_alpha, h_alpha, h_glue, _root_.map_sub, h_zero, h_one, zero_sub, map_neg]
      apply neg_injective
      rw [neg_sub, neg_neg]
      refine sub_eq_of_eq_add (AddMonoidHom.ext fun s ↦ Gm.ext.2 ?_)
      -- The twist sends the power `X^s` to `χ s · X^s`, whose untilt is the root of unity at `s`
      -- times the untilt of `X^s`.
      have h_twist : ρ c (y.down.hom (lift OFlat OFlat[ℚ] ℚ
            (((algebraMap OFlat OFlat[ℚ] : OFlat →* OFlat[ℚ])).comp χ * of OFlat ℚ)
            (of OFlat ℚ (.ofAdd s)))) =
          c.genericStructureMap (algebraMap A ℂ_[ℓ]
              ((compatibleRootsOfUnity (ℓ := ℓ) (A := A)).val (.ofAdd s) : A)) *
            ρ c (y.down.hom (of OFlat ℚ (.ofAdd s))) := by
        erw [lift_of, MonoidHom.mul_apply, map_mul, map_mul, ← hχ, ← ρ_const]
        exact congrArg (fun z ↦ ρ c z * _) (y.down.hom.commutes _)
      refine h_twist.trans ?_
      -- `erw` and `rfl`: `tateGen` is the family of these roots of unity by definition.
      erw [desc_of]
      rfl
  have h_gen : origin ⟨true⟩ ≫ κ = tateGen (genericTestOver A) := hom_ext fun _ _ ↦ rfl
  exact exists_isTodaCancellation_etaClass_of_squares χ f α κ h_torus h_disc h_kummer h_gen

open Period in
/-- Let `O^♭` be the inverse limit of `O_C/ℓ` along `x ↦ x^ℓ`, `M` an `O^♭`-module, and `ℂ_ℓ` an
`A`-algebra. Suppose every perfect `O^♭`-algebra `b` is acyclic for `M` (`h_acyclic_perfect`): on
`ℓ`-adic tests, the functor `S ↦ Hom(b, S^♭)` with coefficients `S ↦ S^♭ ⊗_{O^♭} M` has cohomology
`b ⊗_{O^♭} M`, concentrated in degree 0. Then the tilted theory `tiltTheory` (on `ℓ`-adic tests
along `R ↦ R[1/ℓ]`, with coefficients `R ↦ R^♭ ⊗_{O^♭} M`) satisfies the projective line formula
`H(ℙ¹ × S) = H(S) ⊕ η H(S)`: the classes `1` and `η` are a basis over the cohomology of every
`S`. -/
lemma hasLineFormula_tiltTheory (M : ModuleCat OFlat) [Algebra A ℂ_[ℓ]]
    (h_acyclic_perfect : IsAcyclicOnPerfect (moduleCoeff (tensorCoeff M))) :
    (tiltTheory A M h_acyclic_perfect).HasLineFormula := by
  -- Cancel `η` on the cover of the perfect projective line by two discs.
  obtain ⟨δ, q, B, K, j, y, ω, h_toda⟩ := exists_isTodaCancellation_etaClass (A := A)
  -- Every flat `S ⊗ coker gluing` is acyclic for the coefficient, so `h_toda` applies.
  let Θ : Theory (genericTestOver A) := tiltTheory A M h_acyclic_perfect
  have h_acyclic (S : AbFunctor PadicTest) [HasFlatValues S] (n : ℕ) :
      Subsingleton (H (abTensor S (cokernel gluing)) Θ.functor n) :=
    subsingleton_H_cokernel_gluing (F := Θ.functor)
      (fun c ↦ isCohomEquiv_tensorCoeff_gluing c h_acyclic_perfect) S n
  exact hasLineFormula_of_isTodaCancellation Θ h_toda h_acyclic

end New.Variety

end TiltedLineFormula
