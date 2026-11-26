module

public import Lib.General.LinearAlgebra.Eigenvalues
public import Lib.Weil.Construction.AdelicRepresentation

/-!
# Hyperbolic space and splittings of a hermitian space along isotropic subspaces

A hermitian space `V : New.Space E n s` has Gram matrix `V.J` over `E` and an adelic frame `V.x`
taking it to `New.stdForm E s`. `New.G E s` is the adelic unitary group of that form, and `V.Γ` is
its group of rational points. Here `E` is a CM field (`CMType E`), and `WeilData E` supplies the
purely imaginary `j` (`star j = -j`) used below. The file constructs hyperbolic space together with
its frame, and defines adelic matrices that are orthonormal at the infinite places and integral at
the finite ones. It then studies a splitting, or Witt decomposition,
`V = (range l ⊕ range k) ⊥ i V₀` with `l` and `k` isotropic and dual: it gives the frames and
coordinates of the splitting in adelic form, the Levi and unipotent elements of the stabiliser of
`range k`, the law of a mixed model, and points adapted to the splitting.

## Main definitions and results

* `New.hyperbolicSpace`: the hyperbolic space of rank `2 p` as a `New.Space`, that is, with an
  adelic frame that carries its Gram matrix to the standard form of signs `New.hyperbolicSigns p`
  (`p` times `+1`, `p` times `-1`).
* `New.Exchange.IsOrthoIntegral`: adelic matrices with orthonormal columns at the infinite places
  and integral finite part. The frame of `New.hyperbolicSpace` and its inverse are such
  (`New.Exchange.isOrthoIntegral_hyperbolicSpace`), and the property is stable under products, block
  sums and choice of columns.
* `New.Space.Splitting.levi`, `New.Space.Splitting.radicalElement`: Levi and unipotent elements;
  every `g` with `g k = k a` is a product of the two
  (`New.Space.Splitting.exists_eq_radicalElement_mul_levi`), and the unipotent elements make up the
  unipotent radical (`New.Space.Splitting.exists_eq_radicalElement_iff`).
* `New.Space.Splitting.IsAdapted`: elements of `G` adapted to a splitting and to `t` in `GL_p(𝔸)`;
  they exist (`New.Space.Splitting.exists_isAdapted_and_frame_eq`).
* `New.Space.Splitting.siegelParabolic_sup_symm_eq_top`: if `V₀` is zero, the stabilizers of the
  spans of `k` and of `l` generate the rational unitary group of `V`.
* `New.Space.Splitting.exists_isCompact_rat_mul_radicalElement_mem`: the rational points of the
  unipotent radical are cocompact.

Notions from other files:
* `New.stdForm E s`: the diagonal adelic matrix that is `diag s` at every infinite place and the
  identity at the finite places.
* `New.G.adeleMatrix`: the `n × n` adelic matrix of an element of the adelic unitary group
  `New.G E s`.
* `New.evalInf w`: evaluation of an adele at the infinite place `w`, a ring map to `ℂ`.
* `Ô E`: the integral finite adeles.

## Relation to the literature

Known; see `Lib.Adelic.Witt.IwasawaDecomposition` and `Lib.Weil.MixedModel.ZeroTerm` for sources.
-/

@[expose] public section

noncomputable section

/-! ## Hyperbolic space; matrices orthonormal at infinity and integral -/

namespace New

open NumberField Matrix stdLattice Prod Weil

variable (E : Type _) [Field E] [CMType E] [WeilData E] {n : Type _} [DecidableEq n]
  (p : Type _) [Fintype p] [DecidableEq p] {m q : Type _} [DecidableEq q] [Fintype m]

/-- The sign function on two copies of p that is +1 on the first copy and −1 on the second. -/
abbrev hyperbolicSigns : p ⊕ p → ℤˣ := 1 ⊕ᵥ -1

private lemma hyperbolicSpace_inf_mul :
    ((√2 : ℂ)⁻¹ • (fromBlocks 1 (-1) 1 1 : Matrix (p ⊕ p) (p ⊕ p) ℂ)) *
      ((√2 : ℂ)⁻¹ • fromBlocks 1 1 (-1) 1) = 1 := by
  simp [fromBlocks_multiply, ← ext_iff, ← mul_assoc, ← mul_inv, ← Complex.ofReal_mul,
    Matrix.one_apply]
  grind

private lemma hyperbolicSpace_fin_mul :
    let c := normNegOne (E := E) |>.val.val
    let ϵ : 𝔸f E := stdLattice.traceOneAdele
    (fromBlocks 1 (-c • 1) (ϵ • 1) ((c * star ϵ) • 1) : Matrix (p ⊕ p) (p ⊕ p) (𝔸f E)) *
      (fromBlocks (star ϵ • 1) 1 ((star c * ϵ) • 1) (-star c • 1)) = 1 := by
  intro c ϵ
  have hc : star c * c = -1 := star_normNegOne_mul_self
  have hϵ : ϵ + star ϵ = 1 := traceOneAdele_add_star
  simp only [fromBlocks_multiply, Matrix.mul_one, Matrix.mul_smul, ← fromBlocks_one]
  congr 1 <;> match_scalars
  · linear_combination hϵ - ϵ * hc
  · linear_combination hc
  · linear_combination ϵ * star ϵ * hc
  · linear_combination hϵ - star ϵ * hc

private lemma hyperbolicSpace_gram :
    let c := normNegOne (E := E) |>.val.val
    let ϵ : 𝔸f E := stdLattice.traceOneAdele
    let x := mkAdelicGL
      (fun _ ↦ Units.mkOfMulEqOne
        ((√2 : ℂ)⁻¹ • (fromBlocks 1 (-1) 1 1 : Matrix (p ⊕ p) (p ⊕ p) ℂ))
        ((√2 : ℂ)⁻¹ • fromBlocks 1 1 (-1) 1) (hyperbolicSpace_inf_mul p),
        Units.mkOfMulEqOne
          (fromBlocks 1 (-c • 1) (ϵ • 1) ((c * star ϵ) • 1) : Matrix (p ⊕ p) (p ⊕ p) (𝔸f E))
          (fromBlocks (star ϵ • 1) 1 ((star c * ϵ) • 1) (-star c • 1))
          (hyperbolicSpace_fin_mul E p))
    x.valᴴ * (fromBlocks (0 : Matrix p p E) 1 1 0).map toAdele * x.val =
      stdForm E (hyperbolicSigns p) := by
  intro c ϵ x
  refine gram_mkAdelicGL ?_ ?_
  · simp [signMatrix, fromBlocks_conjTranspose, fromBlocks_map, fromBlocks_multiply, ← ext_iff,
      ← mul_assoc, ← mul_inv, ← Complex.ofReal_mul, diagonal_apply, Matrix.one_apply]
    grind
  · -- With `b` the finite part of the frame, `bᴴ * J` is the inverse of `b` given above, so
    -- the claim is `b⁻¹ * b = 1`.
    have h_inv : (fromBlocks 1 (-c • 1) (ϵ • 1) ((c * star ϵ) • 1) :
        Matrix (p ⊕ p) (p ⊕ p) (𝔸f E))ᴴ *
          (fromBlocks 0 1 1 0 : Matrix (p ⊕ p) (p ⊕ p) E).map (algebraMap E (𝔸f E)) =
        fromBlocks (star ϵ • 1) 1 ((star c * ϵ) • 1) (-star c • 1) := by
      simp [fromBlocks_conjTranspose, fromBlocks_map, fromBlocks_multiply]
    exact (congrArg (· * _) h_inv).trans (Units.inv_mul ⟨_, _, _, _⟩)

/-- Hyperbolic space of rank `2 p`: the Gram matrix has blocks `(0, 1; 1, 0)`, and the adelic frame
carries it to the standard form with signs `+1` on the first `p` and `−1` on the last `p`
coordinates. The frame is `(1/√2) (1, −1; 1, 1)` at every infinite place and `(1, −c; ϵ, c ϵ̄)` at
the finite places, with `c` the integral unit `New.Weil.normNegOne` (`c̄ c = −1`) and
`ϵ = stdLattice.traceOneAdele` (`ϵ + ϵ̄ = 1`). -/
@[simps J]
noncomputable def hyperbolicSpace : Space E (p ⊕ p) (hyperbolicSigns p) :=
  let c := normNegOne.val.val
  let ϵ : 𝔸f E := stdLattice.traceOneAdele
  { J := fromBlocks 0 1 1 0
    x := mkAdelicGL
      (fun _ ↦ Units.mkOfMulEqOne
        ((√2 : ℂ)⁻¹ • fromBlocks 1 (-1) 1 1) ((√2 : ℂ)⁻¹ • fromBlocks 1 1 (-1) 1)
        (by exact hyperbolicSpace_inf_mul p),
        Units.mkOfMulEqOne
          (fromBlocks 1 (-c • 1) (ϵ • 1) ((c * star ϵ) • 1))
          (fromBlocks (star ϵ • 1) 1 ((star c * ϵ) • 1) (-star c • 1))
          (by exact hyperbolicSpace_fin_mul E p))
    gram_point := by exact hyperbolicSpace_gram E p }

variable {E p}

lemma signs_comp_refl {m : Sort*} {t : m → ℤˣ} : t ∘ Equiv.refl m = t := rfl

/-- An adelic matrix `M` is orthonormal at infinity and integral: `M_wᴴ M_w = 1` at every infinite
place `w`, where `M_w` is the complex matrix of the components of `M` at `w`, and every entry of
`M` has its finite part in `Ô E`. -/
@[local simp]
def Exchange.IsOrthoIntegral {E : Type _} [Field E] [NumberField E] (M : Matrix m n (𝔸 E)) : Prop :=
  (∀ w : InfinitePlace E, (M.map (evalInf w))ᴴ * M.map (evalInf w) = 1) ∧
  ∀ (i : m) (k : n), (M i k).2 ∈ Ô E

/-- The adelic frame `x` of hyperbolic space is orthonormal at infinity and integral. -/
lemma Exchange.isOrthoIntegral_hyperbolicSpace_x : IsOrthoIntegral (hyperbolicSpace E p).x.val := by
  -- The entries are integral; at the infinite places the diagonal entries of
  -- `(1/√2)² (2 · 1)` are `2⁻¹ + 2⁻¹ = 1`.
  have h_half : (2⁻¹ : ℂ) + 2⁻¹ = 1 := by norm_num
  refine ⟨fun w ↦ ?_, ?_⟩
  · simp [hyperbolicSpace, ← ext_iff, Matrix.mul_apply, Matrix.one_apply, ← mul_inv,
      ← Complex.ofReal_mul, ite_add_ite, h_half, eq_comm]
  · simp [hyperbolicSpace, ite_mem, star_mem_Ô, traceOneAdele_mem, mul_mem, Matrix.one_apply]

/-- The inverse `x⁻¹` of the adelic frame of hyperbolic space is orthonormal at infinity and
integral. -/
lemma Exchange.isOrthoIntegral_hyperbolicSpace_x_inv :
    IsOrthoIntegral (hyperbolicSpace E p).x⁻¹.val := by
  have h_half : (2⁻¹ : ℂ) + 2⁻¹ = 1 := by norm_num
  refine ⟨fun w ↦ ?_, ?_⟩
  · simp [hyperbolicSpace, Units.mkOfMulEqOne, ← map_inv, ← ext_iff, Matrix.mul_apply,
      Matrix.one_apply, ← mul_inv, ← Complex.ofReal_mul, ite_add_ite, h_half, eq_comm]
  · simp [hyperbolicSpace, Units.mkOfMulEqOne, ← map_inv, ite_mem, star_mem_Ô, traceOneAdele_mem,
      mul_mem, Matrix.one_apply]

/-- For the hyperbolic space `hyperbolicSpace E p` of rank `2 p` (Gram matrix with blocks
`(0, 1; 1, 0)`), consider its adelic frame `x`, which carries the Gram matrix to the signed standard
form with signs `+1` on the first `p` and `−1` on the last `p` coordinates. Both `x` and its inverse
`x⁻¹` are orthonormal at infinity and integral: at each infinite place `w` the complex matrix `M_w`
of components satisfies `M_wᴴ M_w = 1` (unitary for the standard definite form), and every entry has
finite part in `Ô E`. -/
lemma Exchange.isOrthoIntegral_hyperbolicSpace :
    IsOrthoIntegral (hyperbolicSpace E p).x.val ∧ IsOrthoIntegral (hyperbolicSpace E p).x⁻¹.val :=
  ⟨isOrthoIntegral_hyperbolicSpace_x, isOrthoIntegral_hyperbolicSpace_x_inv⟩

namespace Exchange.IsOrthoIntegral

omit [WeilData E] in
lemma of_stdForm [Fintype n] (s : n → ℤˣ) : IsOrthoIntegral (stdForm E s) := by
  simp [stdForm, apply_ite, ← Int.cast_mul, diagonal_apply]

omit [WeilData E] in
lemma one [Fintype n] :
    IsOrthoIntegral (1 : Matrix n n (𝔸 E)) := by aesop (add simp Matrix.one_apply)

variable {A : Matrix m n (𝔸 E)} (hA : IsOrthoIntegral A)

include hA

section

omit [WeilData E]

/-- The first half of `IsOrthoIntegral A`: `A_wᴴ A_w = 1` at each infinite place `w`, where `A_w` is
the complex matrix `A.map (evalInf w)`. -/
lemma conjTranspose_map_mul_map (w : InfinitePlace E) :
    (A.map (evalInf w))ᴴ * A.map (evalInf w) = 1 := hA.left w

/-- The second half of `IsOrthoIntegral A`: every entry of `A` has its finite part in `Ô E`. -/
lemma snd_mem_Ô (i : m) (k : n) : (A i k).2 ∈ Ô E := hA.right i k

/-- A product of matrices orthonormal at infinity and integral is again such. -/
lemma mul [Fintype n]
    {B : Matrix n q (𝔸 E)} (hB : IsOrthoIntegral B) : IsOrthoIntegral (A * B) := by
  refine ⟨fun w ↦ ?_, fun i k ↦ ?_⟩
  · -- Evaluation at `w` is multiplicative, and `Bᴴ Aᴴ A B = Bᴴ B = 1`.
    rw [Matrix.map_mul, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (A.map _)ᴴ,
      hA.conjTranspose_map_mul_map w, Matrix.one_mul, hB.conjTranspose_map_mul_map w]
  · -- The finite part of an entry of `A * B` is a sum of products of integral finite parts.
    simp [Matrix.mul_apply, snd_sum, sum_mem, mul_mem, hA.snd_mem_Ô, hB.snd_mem_Ô]

omit [DecidableEq p] in
/-- A block sum of matrices orthonormal at infinity and integral is again such. -/
lemma block_diag {B : Matrix p q (𝔸 E)} (hB : IsOrthoIntegral B) :
    IsOrthoIntegral (fromBlocks A 0 0 B) := by
  refine ⟨fun w ↦ ?_, ?_⟩
  · -- At `w` the matrix is block diagonal with the blocks `A_w` and `B_w`.
    simp [fromBlocks_map, fromBlocks_conjTranspose, fromBlocks_multiply,
      hA.conjTranspose_map_mul_map w, hB.conjTranspose_map_mul_map w]
  · -- Each entry is an entry of `A`, an entry of `B`, or zero.
    simp [Sum.forall, hA.snd_mem_Ô, hB.snd_mem_Ô]

/-- If `B = A.submatrix id e * C`, that is, the matrix of the columns `e j` of `A` times `C`, where
`e` is injective, and `A` and `C` are orthonormal at infinity and integral, then so is `B`. When
`he` is not given, `simp` proves that `e` is injective. -/
lemma of_eq_submatrix_mul {C : Matrix p q (𝔸 E)} (e : p → n) (hC : IsOrthoIntegral C)
    {B : Matrix m q (𝔸 E)} (h_eq : B = A.submatrix id e * C)
    (he : e.Injective := by simp [Function.Injective]) : IsOrthoIntegral B := by
  -- Selecting distinct columns of `A` keeps them orthonormal and integral: at `w` the Gram matrix
  -- of the chosen columns is the `(e, e)` block of that of `A`, which is `1` as `e` is injective.
  have h_cols : IsOrthoIntegral (A.submatrix id e) := by
    refine ⟨fun w ↦ ?_, fun i j ↦ hA.snd_mem_Ô i (e j)⟩
    rw [← submatrix_map, conjTranspose_submatrix, ← submatrix_mul _ _ e id e Function.bijective_id,
      hA.conjTranspose_map_mul_map w, submatrix_one e he]
  subst h_eq
  exact h_cols.mul hC

end

end Exchange.IsOrthoIntegral

end New

/-! ## Splitting along isotropic subspaces: Levi and unipotent parts -/

section Splitting

namespace New

open NumberField Matrix WeilData Exchange Fintype G Function

section

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n n₁ : Type*} [Fintype n]
  [DecidableEq n] {s : n → ℤˣ} (g : G E s)

/-- An element `g` of the adelic unitary group preserves the standard form: `gᴴ S g = S`, with
`S = stdForm E s`. -/
lemma G.conjTranspose_adeleMatrix_mul_stdForm_mul_adeleMatrix :
    g.adeleMatrixᴴ * stdForm E s * g.adeleMatrix = stdForm E s :=
  mem_unitaryGroupOf_iff.1 g.toUnitary.prop

omit [IsCMField E] in
/-- The standard form `S = stdForm E s` is its own inverse: `S (S a) = a`. -/
@[simp]
lemma stdForm_mul_stdForm_mul (a : Matrix n n₁ (𝔸 E)) : stdForm E s * (stdForm E s * a) = a := by
  simp [← Matrix.mul_assoc]

/-- The inverse of `g` has the matrix `S gᴴ S`, with `S = stdForm E s`. -/
lemma G.adeleMatrix_inv : g⁻¹.adeleMatrix = stdForm E s * g.adeleMatrixᴴ * stdForm E s :=
  U.coe_inv (by simp) g.toUnitary

end

variable {E : Type*} [Field E] [CMType E] {n n₁ : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  [Fintype n₁] [DecidableEq n₁] {s₁ : n₁ → ℤˣ} (g : G E s) {V₁ : Space E n₁ s₁} (V : Space E n s)

/-- For a matrix `i` over `E`, its adelic form `V.ratMap V₁ i = x⁻¹ i x₁`, with `x`, `x₁` the adelic
frames of `V`, `V₁`, sends the adelic vector `x₁⁻¹ y` of a rational vector `y` to the adelic
vector `x⁻¹ (i y)`. -/
lemma Space.ratMap_mulVec_vecAtPoint (i : Matrix n n₁ E) (y : n₁ → E) :
    V.ratMap V₁ i *ᵥ V₁.vecAtPoint y = V.vecAtPoint (i *ᵥ y) := by
  simp [ratMap, vecAtPoint, comp_def, RingHom.map_mulVec]

/-- For matrices `A`, `B` over `E`, the Gram matrix of `x⁻¹ A` and `x⁻¹ B` for the standard form is
the adelic image of the Gram matrix `Aᴴ J B` of `V`; here `x` is the adelic frame of `V`. -/
lemma Space.gram_at_point_eq_map {a b : Type*} (A : Matrix n a E) (B : Matrix n b E) :
    (V.x⁻¹.val * A.map toAdele)ᴴ * stdForm E s * (V.x⁻¹.val * B.map toAdele) =
      (Aᴴ * V.J * B).map toAdele := by
  simp [map_J, Matrix.mul_assoc]

variable [WeilData E] {n₀ p q : Type*} [Fintype n₀] [DecidableEq n₀] [Fintype p] [DecidableEq p]
  {s₀ : n₀ → ℤˣ} (V₀ : Space E n₀ s₀)

/-! ### Splittings -/

/-- A Witt decomposition `V = (l E^p ⊕ k E^p) ⊥ i V₀` over `E`: isotropic frames `l`, `k` with
`lᴴ J k = 1`, an isometry `i` from `V₀` orthogonal to both, and `rk V = rk V₀ + 2 p`. -/
structure Space.Splitting (p : Type*) [Fintype p] [DecidableEq p] where
  /-- The frame k, whose columns span one isotropic subspace. -/
  k : Matrix n p E
  /-- The frame l, whose columns span the dual isotropic subspace. -/
  l : Matrix n p E
  /-- The matrix i of the embedding of V₀ into V. -/
  i : Matrix n n₀ E
  /-- `k` is isotropic: `kᴴ J k = 0`. -/
  gram_kk : kᴴ * V.J * k = 0
  /-- `l` is isotropic: `lᴴ J l = 0`. -/
  gram_ll : lᴴ * V.J * l = 0
  /-- `l` and `k` are dual: `lᴴ J k = 1`. -/
  gram_lk : lᴴ * V.J * k = 1
  /-- `i` is an isometry: `iᴴ J i` is the Gram matrix `V₀.J` of `V₀`. -/
  gram_ii : iᴴ * V.J * i = V₀.J
  /-- The image of i is orthogonal to k. -/
  gram_ik : iᴴ * V.J * k = 0
  /-- The image of i is orthogonal to l. -/
  gram_il : iᴴ * V.J * l = 0
  /-- The rank of V is the rank of V₀ plus twice the number of columns of k. -/
  protected card_eq : card n = card n₀ + 2 * card p

variable (p) in
/-- The orthogonal sum of hyperbolic space of rank 2p and V₀. -/
def Exchange.hyperbolicSum : Space E ((p ⊕ p) ⊕ n₀) (hyperbolicSigns p ⊕ᵥ s₀) :=
  (hyperbolicSpace E p).sum V₀

variable {V V₀}

/-- The splitting of `V` over `V₀` whose frames `l`, `k` and embedding `i` are the three column
blocks of a matrix `M` over `E`, given that `Mᴴ J M` is the Gram matrix of hyperbolic space plus
`V₀` (the hypothesis `h_gram`) and that the ranks agree (the hypothesis `h_card`). -/
def Exchange.splittingOfGram (M : Matrix n ((p ⊕ p) ⊕ n₀) E)
    (h_gram : Mᴴ * V.J * M = (hyperbolicSum p V₀).J) (h_card : card n = card n₀ + 2 * card p) :
    V.Splitting V₀ p where
  k := M.toCols₁.toCols₂
  l := M.toCols₁.toCols₁
  i := M.toCols₂
  -- Each relation is a block of the Gram matrix `h_gram`.
  gram_kk := Matrix.ext fun _ _ ↦ congrFun₂ h_gram _ _
  gram_ll := Matrix.ext fun _ _ ↦ congrFun₂ h_gram _ _
  gram_lk := Matrix.ext fun _ _ ↦ congrFun₂ h_gram _ _
  gram_ii := Matrix.ext fun _ _ ↦ congrFun₂ h_gram _ _
  gram_ik := Matrix.ext fun _ _ ↦ congrFun₂ h_gram _ _
  gram_il := Matrix.ext fun _ _ ↦ congrFun₂ h_gram _ _
  card_eq := h_card

end New

namespace New

open NumberField Matrix WeilData Exchange Fintype G Function

variable {E : Type*} [Field E] [CMType E] {n n₁ : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  [Fintype n₁] [DecidableEq n₁] {s₁ : n₁ → ℤˣ} {g : G E s} {V₁ : Space E n₁ s₁} {V : Space E n s}
  [WeilData E] {n₀ p q : Type*} [Fintype n₀] [DecidableEq n₀] [Fintype p] [DecidableEq p]
  {s₀ : n₀ → ℤˣ} {V₀ : Space E n₀ s₀} (D : V.Splitting V₀ p) {a : Matrix p p (𝔸 E)}
  (c : Matrix n₀ p (𝔸 E)) (b : Matrix p p (𝔸 E))

namespace Space.Splitting

/-! ### Adelic frames and dual coordinates -/

/-- For a splitting of V, the adelic n×p matrix x⁻¹k, x the adelic frame of V: the isotropic
frame k in standard coordinates. -/
def kAdelic : Matrix n p (𝔸 E) := V.x⁻¹.val * D.k.map toAdele

/-- For a splitting of V, the adelic n×p matrix x⁻¹l, x the adelic frame of V: the isotropic
frame l in standard coordinates. -/
def lAdelic : Matrix n p (𝔸 E) := V.x⁻¹.val * D.l.map toAdele

/-- For a splitting of V over V₀, the adelic matrix ι = x⁻¹ i x₀, with x, x₀ the adelic frames:
the embedding i in standard coordinates. -/
def iAdelic : Matrix n n₀ (𝔸 E) := V.ratMap V₀ D.i

section

omit [WeilData E]

lemma gram_kl : D.kᴴ * V.J * D.l = 1 := by
  rw [V.conjTranspose_mul_J_mul_swap, D.gram_lk, conjTranspose_one]

lemma gram_ki : D.kᴴ * V.J * D.i = 0 := by
  rw [V.conjTranspose_mul_J_mul_swap, D.gram_ik, conjTranspose_zero]

/-- The splitting of V obtained from a given one by exchanging the two isotropic frames k and l
and keeping the embedding i. -/
def symm : V.Splitting V₀ p where
  k := D.l
  l := D.k
  i := D.i
  gram_kk := D.gram_ll
  gram_ll := D.gram_kk
  gram_lk := D.gram_kl
  gram_ii := D.gram_ii
  gram_ik := D.gram_il
  gram_il := D.gram_ik
  card_eq := D.card_eq

lemma gram_li : D.lᴴ * V.J * D.i = 0 := by
  rw [V.conjTranspose_mul_J_mul_swap, D.gram_il, conjTranspose_zero]

end

attribute [simp high] gram_kk gram_ll gram_lk gram_kl gram_ii gram_ik gram_il gram_ki gram_li

/-- For a splitting, the adelic `p × n` matrix `lAdelicᴴ ε`, with `ε = stdForm E s`; it sends
`lAdelic a + iAdelic w + kAdelic b` to `b`. -/
def kCoord : Matrix p n (𝔸 E) := D.lAdelicᴴ * stdForm E s

/-- For a splitting, the adelic `n₀ × n` matrix `ε₀ iAdelicᴴ ε`, the adjoint of the adelic embedding
`iAdelic` for the standard forms `ε`, `ε₀` of `V`, `V₀`; it sends
`lAdelic a + iAdelic w + kAdelic b` to `w`. -/
def iCoord : Matrix n₀ n (𝔸 E) := stdForm E s₀ * D.iAdelicᴴ * stdForm E s

/-- For a splitting, the adelic `p × n` matrix `kAdelicᴴ ε`, with `ε = stdForm E s`; it sends
`lAdelic a + iAdelic w + kAdelic b` to `a`. -/
def lCoord : Matrix p n (𝔸 E) := D.kAdelicᴴ * stdForm E s

-- The coordinates are dual to the frames: each product is the adelic image of a Gram matrix
-- `Aᴴ J B` of two of `k`, `l`, `i` (`Space.gram_at_point_eq_map`), which a relation of `D` gives.
-- For `iCoord`, the frame `x₀` of `V₀` and the standard form `ε₀` of `V₀` stand on the left;
-- then `x₀ᴴ J₀ x₀ = ε₀` and `ε₀ ε₀ = 1`.

section

omit [WeilData E]

lemma kCoord_mul_kAdelic : D.kCoord * D.kAdelic = 1 := by
  simpa [kCoord, lAdelic, kAdelic, D.gram_lk] using V.gram_at_point_eq_map D.l D.k

lemma kCoord_mul_lAdelic : D.kCoord * D.lAdelic = 0 := by
  simpa [kCoord, lAdelic, D.gram_ll] using V.gram_at_point_eq_map D.l D.l

lemma kCoord_mul_iAdelic : D.kCoord * D.iAdelic = 0 := by
  rw [kCoord, lAdelic, iAdelic, ratMap, ← Matrix.mul_assoc, V.gram_at_point_eq_map, D.gram_li]
  simp

lemma lCoord_mul_kAdelic : D.lCoord * D.kAdelic = 0 := by
  simpa [lCoord, kAdelic, D.gram_kk] using V.gram_at_point_eq_map D.k D.k

lemma lCoord_mul_lAdelic : D.lCoord * D.lAdelic = 1 := by
  simpa [lCoord, kAdelic, lAdelic, D.gram_kl] using V.gram_at_point_eq_map D.k D.l

lemma lCoord_mul_iAdelic : D.lCoord * D.iAdelic = 0 := by
  rw [lCoord, kAdelic, iAdelic, ratMap, ← Matrix.mul_assoc, V.gram_at_point_eq_map, D.gram_ki]
  simp

lemma iCoord_mul_kAdelic : D.iCoord * D.kAdelic = 0 := by
  simp [iCoord, kAdelic, iAdelic, ratMap, ← V.gram_point, conjTranspose_nonsing_inv,
    Matrix.mul_assoc, ← Matrix.map_mul]
  rw [← Matrix.mul_assoc D.iᴴ V.J, D.gram_ik]
  simp

lemma iCoord_mul_lAdelic : D.iCoord * D.lAdelic = 0 := by
  simp [iCoord, lAdelic, iAdelic, ratMap, ← V.gram_point, conjTranspose_nonsing_inv,
    Matrix.mul_assoc, ← Matrix.map_mul]
  rw [← Matrix.mul_assoc D.iᴴ V.J, D.gram_il]
  simp

lemma iCoord_mul_iAdelic : D.iCoord * D.iAdelic = 1 := by
  have h_point₀ : V₀.x.valᴴ * (V₀.J.map toAdele * V₀.x.val) = stdForm E s₀ := by
    rw [← Matrix.mul_assoc, V₀.gram_point]
  suffices h : stdForm E s₀ * (V₀.x.valᴴ * (D.iᴴ.map toAdele *
      (V.J.map toAdele * (D.i.map toAdele * V₀.x.val)))) = 1 by
    simpa [iCoord, iAdelic, ratMap, ← V.gram_point, conjTranspose_nonsing_inv, Matrix.mul_assoc]
      using h
  rw [← Matrix.mul_assoc (V.J.map toAdele), ← Matrix.mul_assoc (D.iᴴ.map toAdele),
    ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc D.iᴴ V.J, D.gram_ii]
  simp [h_point₀]

/-- For a splitting, the three coordinate matrices along k, l and V₀ are dual to the adelic frames
k, l, ι: each times its own frame is the identity, and times either other frame is zero. -/
@[simp]
lemma coord_mul_frame :
    (D.kCoord * D.kAdelic = 1 ∧ D.kCoord * D.lAdelic = 0 ∧ D.kCoord * D.iAdelic = 0) ∧
    (D.lCoord * D.kAdelic = 0 ∧ D.lCoord * D.lAdelic = 1 ∧ D.lCoord * D.iAdelic = 0) ∧
    D.iCoord * D.kAdelic = 0 ∧ D.iCoord * D.lAdelic = 0 ∧ D.iCoord * D.iAdelic = 1 :=
  ⟨⟨D.kCoord_mul_kAdelic, D.kCoord_mul_lAdelic, D.kCoord_mul_iAdelic⟩,
    ⟨D.lCoord_mul_kAdelic, D.lCoord_mul_lAdelic, D.lCoord_mul_iAdelic⟩,
    D.iCoord_mul_kAdelic, D.iCoord_mul_lAdelic, D.iCoord_mul_iAdelic⟩

lemma conjTranspose_kCoord : D.kCoordᴴ = stdForm E s * D.lAdelic := by simp [kCoord]

lemma conjTranspose_lCoord : D.lCoordᴴ = stdForm E s * D.kAdelic := by simp [lCoord]

lemma conjTranspose_iCoord : D.iCoordᴴ = stdForm E s * D.iAdelic * stdForm E s₀ := by
  simp [iCoord, Matrix.mul_assoc]

end

omit [WeilData E] in
/-- The adjoints of the three coordinate matrices, written through the adelic frames and the
standard forms. -/
@[local simp]
lemma conjTranspose_coord :
    D.kCoordᴴ = stdForm E s * D.lAdelic ∧
    D.lCoordᴴ = stdForm E s * D.kAdelic ∧
    D.iCoordᴴ = stdForm E s * D.iAdelic * stdForm E s₀ :=
  ⟨D.conjTranspose_kCoord, D.conjTranspose_lCoord, D.conjTranspose_iCoord⟩

-- The relations above followed by a further factor `X`, in the right-bracketed form that `simp`
-- meets: a coordinate matrix applied to a combination of the columns of one frame gives its
-- coefficients.

section

omit [WeilData E]

lemma kCoord_mul_kAdelic_mul {m : Type*} (X : Matrix p m (𝔸 E)) :
    D.kCoord * (D.kAdelic * X) = X := by simp [← Matrix.mul_assoc, D.kCoord_mul_kAdelic]

lemma iCoord_mul_kAdelic_mul {m : Type*} (X : Matrix p m (𝔸 E)) :
    D.iCoord * (D.kAdelic * X) = 0 := by simp [← Matrix.mul_assoc, D.iCoord_mul_kAdelic]

lemma lCoord_mul_kAdelic_mul {m : Type*} (X : Matrix p m (𝔸 E)) :
    D.lCoord * (D.kAdelic * X) = 0 := by simp [← Matrix.mul_assoc, D.lCoord_mul_kAdelic]

lemma kCoord_mul_lAdelic_mul {m : Type*} (X : Matrix p m (𝔸 E)) :
    D.kCoord * (D.lAdelic * X) = 0 := by simp [← Matrix.mul_assoc, D.kCoord_mul_lAdelic]

lemma iCoord_mul_lAdelic_mul {m : Type*} (X : Matrix p m (𝔸 E)) :
    D.iCoord * (D.lAdelic * X) = 0 := by simp [← Matrix.mul_assoc, D.iCoord_mul_lAdelic]

lemma lCoord_mul_lAdelic_mul {m : Type*} (X : Matrix p m (𝔸 E)) :
    D.lCoord * (D.lAdelic * X) = X := by simp [← Matrix.mul_assoc, D.lCoord_mul_lAdelic]

lemma kCoord_mul_iAdelic_mul {m : Type*} (X : Matrix n₀ m (𝔸 E)) :
    D.kCoord * (D.iAdelic * X) = 0 := by simp [← Matrix.mul_assoc, D.kCoord_mul_iAdelic]

lemma iCoord_mul_iAdelic_mul {m : Type*} (X : Matrix n₀ m (𝔸 E)) :
    D.iCoord * (D.iAdelic * X) = X := by simp [← Matrix.mul_assoc, D.iCoord_mul_iAdelic]

lemma lCoord_mul_iAdelic_mul {m : Type*} (X : Matrix n₀ m (𝔸 E)) :
    D.lCoord * (D.iAdelic * X) = 0 := by simp [← Matrix.mul_assoc, D.lCoord_mul_iAdelic]

-- The pairings of the frames with the standard form are coordinate matrices.

/-- Pairing with `lAdelic` under the standard form is the `k`-coordinate matrix. -/
lemma conjTranspose_lAdelic_mul_stdForm_mul {m : Type*} (X : Matrix n m (𝔸 E)) :
    D.lAdelicᴴ * (stdForm E s * X) = D.kCoord * X := by rw [kCoord, Matrix.mul_assoc]

/-- Pairing with `iAdelic` under the standard form is the `V₀`-coordinate matrix followed by the
standard form of `V₀`. -/
lemma conjTranspose_iAdelic_mul_stdForm_mul {m : Type*} (X : Matrix n m (𝔸 E)) :
    D.iAdelicᴴ * (stdForm E s * X) = stdForm E s₀ * (D.iCoord * X) := by
  simp [iCoord, ← Matrix.mul_assoc, stdForm_mul_self]

/-- The relations of `New.Space.Splitting.coord_mul_frame` followed by a further factor `X`, in the
right-bracketed form that `simp` meets. The first two groups say that a coordinate matrix applied to
a combination of the columns of one frame gives its coefficients. The last group says that the
pairing with `kAdelic` or `lAdelic` under the standard form is a coordinate matrix, and the pairing
with `iAdelic` is the `V₀` coordinate matrix followed by the standard form of `V₀`. -/
@[simp]
lemma coord_mul_frame_mul {m : Type*} :
    (∀ X : Matrix p m (𝔸 E),
      D.kCoord * (D.kAdelic * X) = X ∧
      D.iCoord * (D.kAdelic * X) = 0 ∧
      D.lCoord * (D.kAdelic * X) = 0 ∧
      D.kCoord * (D.lAdelic * X) = 0 ∧
      D.iCoord * (D.lAdelic * X) = 0 ∧
      D.lCoord * (D.lAdelic * X) = X) ∧
    (∀ X : Matrix n₀ m (𝔸 E),
      D.kCoord * (D.iAdelic * X) = 0 ∧
      D.iCoord * (D.iAdelic * X) = X ∧
      D.lCoord * (D.iAdelic * X) = 0) ∧
    ∀ X : Matrix n m (𝔸 E),
      D.kAdelicᴴ * (stdForm E s * X) = D.lCoord * X ∧
      D.lAdelicᴴ * (stdForm E s * X) = D.kCoord * X ∧
      D.iAdelicᴴ * (stdForm E s * X) = stdForm E s₀ * (D.iCoord * X) :=
  ⟨fun X ↦ ⟨D.kCoord_mul_kAdelic_mul X, D.iCoord_mul_kAdelic_mul X, D.lCoord_mul_kAdelic_mul X,
      D.kCoord_mul_lAdelic_mul X, D.iCoord_mul_lAdelic_mul X, D.lCoord_mul_lAdelic_mul X⟩,
    fun X ↦ ⟨D.kCoord_mul_iAdelic_mul X, D.iCoord_mul_iAdelic_mul X, D.lCoord_mul_iAdelic_mul X⟩,
    fun X ↦ ⟨by rw [lCoord, Matrix.mul_assoc], D.conjTranspose_lAdelic_mul_stdForm_mul X,
      D.conjTranspose_iAdelic_mul_stdForm_mul X⟩⟩

/-- The frames and coordinate matrices of a splitting resolve the identity, so every adelic vector
is the sum of its components along `kAdelic`, `iAdelic` and `lAdelic`. -/
lemma sum_frame_mul_coord_eq_one :
    D.kAdelic * D.kCoord + D.iAdelic * D.iCoord + D.lAdelic * D.lCoord = 1 := by
  -- The block matrices `(kAdelic iAdelic lAdelic)` and `(kCoord; iCoord; lCoord)` have product `1`
  -- in the order coordinates times frames, by `coord_mul_frame`. They are square by `D.card_eq`,
  -- so their product in the other order is `1` too, and that product is the sum in the claim.
  have h_card : card ((p ⊕ n₀) ⊕ p) = card n := by simp +arith [D.card_eq]
  have h_coord_frame : (D.kCoord.fromRows D.iCoord).fromRows D.lCoord *
      (D.kAdelic.fromCols D.iAdelic).fromCols D.lAdelic = 1 := by
    rw [fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul, mul_fromCols]
    simp [coord_mul_frame]
  rwa [mul_eq_one_comm_of_card_eq _ _ _ h_card, fromCols_mul_fromRows,
    fromCols_mul_fromRows] at h_coord_frame

/-- `g` acts on the isotropic frame `k` of the splitting by the matrix `c`: `g k = k c` in adelic
coordinates. -/
@[simp]
abbrev ActsOnFrame (g : G E s) (c : Matrix p p (𝔸 E)) : Prop :=
  g.adeleMatrix * D.kAdelic = D.kAdelic * c

/-- If an element `g` of `G E s` acts on the adelic frame `kAdelic` by an invertible `a`
(`g k = k a`), then `g` multiplies the `l`-coordinate by `a⁻ᴴ`: `lCoord g = a⁻ᴴ lCoord`. -/
lemma lCoord_mul_adeleMatrix {a : GL p (𝔸 E)} (hk : D.ActsOnFrame g a.val) :
    D.lCoord * g.adeleMatrix = a⁻¹.valᴴ * D.lCoord := by
  -- As `g k = k a`, the frame `k` is `g k a⁻¹`; take the adjoint and use that `g` preserves the
  -- standard form.
  have h_k : D.kAdelic = g.adeleMatrix * D.kAdelic * a⁻¹.val := by simp [hk]
  calc D.lCoord * g.adeleMatrix
    _ = (g.adeleMatrix * D.kAdelic * a⁻¹.val)ᴴ * stdForm E s * g.adeleMatrix := by
      rw [← h_k, lCoord]
    _ = a⁻¹.valᴴ * D.kAdelicᴴ * (g.adeleMatrixᴴ * stdForm E s * g.adeleMatrix) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = a⁻¹.valᴴ * D.lCoord := by
      rw [g.conjTranspose_adeleMatrix_mul_stdForm_mul_adeleMatrix, lCoord, Matrix.mul_assoc]

/-- If an element `g` of `G E s` acts on the adelic frame `kAdelic` by a matrix `a`
(`g k = k a`), then `a` is invertible. -/
lemma ActsOnFrame.isUnit (hk : D.ActsOnFrame g a) : IsUnit a := by
  -- `kCoord g⁻¹ k` is a left inverse of `a`: `kCoord g⁻¹ k a = kCoord g⁻¹ g k = kCoord k = 1`.
  have h_left_inv : D.kCoord * g.adeleMatrix⁻¹ * D.kAdelic * a = 1 := by
    rw [Matrix.mul_assoc, ← hk, Matrix.mul_assoc]
    simp [adeleMatrix, coord_mul_frame]
  exact .of_mul_eq_one_right _ h_left_inv

end

/-! ### The Levi subgroup, and composition of splittings -/

omit [WeilData E] in
private lemma conjTranspose_kAdelic_mul_stdForm_mul {m : Type*} (X : Matrix n m (𝔸 E)) :
    D.kAdelicᴴ * (stdForm E s * X) = D.lCoord * X := by
  rw [lCoord, Matrix.mul_assoc]

omit [WeilData E] in
/-- Two adelic `n × n` matrices are equal when they agree on each of the three adelic frames `k`,
`i` and `l` of a splitting. -/
private lemma eq_of_mul_kAdelic_of_mul_iAdelic_of_mul_lAdelic {M N : Matrix n n (𝔸 E)}
    (h_k : M * D.kAdelic = N * D.kAdelic) (h_i : M * D.iAdelic = N * D.iAdelic)
    (h_l : M * D.lAdelic = N * D.lAdelic) : M = N := by
  -- Multiply both by `1`, written as `k kCoord + i iCoord + l lCoord`.
  rw [← M.mul_one, ← N.mul_one, ← D.sum_frame_mul_coord_eq_one]
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, h_k, h_i, h_l]

omit [WeilData E] in
private lemma leviMatrix_mul_kAdelic (x : GL p (𝔸 E) × G E s₀) :
    (D.kAdelic * x.fst.val * D.kCoord + D.iAdelic * x.snd.adeleMatrix * D.iCoord +
      D.lAdelic * (x.fst⁻¹).valᴴ * D.lCoord) * D.kAdelic = D.kAdelic * x.fst.val := by
  simp only [Matrix.add_mul, Matrix.mul_assoc, D.kCoord_mul_kAdelic, D.iCoord_mul_kAdelic,
    D.lCoord_mul_kAdelic, Matrix.mul_one, Matrix.mul_zero, add_zero]

omit [WeilData E] in
private lemma leviMatrix_mul_iAdelic (x : GL p (𝔸 E) × G E s₀) :
    (D.kAdelic * x.fst.val * D.kCoord + D.iAdelic * x.snd.adeleMatrix * D.iCoord +
      D.lAdelic * (x.fst⁻¹).valᴴ * D.lCoord) * D.iAdelic = D.iAdelic * x.snd.adeleMatrix := by
  simp only [Matrix.add_mul, Matrix.mul_assoc, D.kCoord_mul_iAdelic, D.iCoord_mul_iAdelic,
    D.lCoord_mul_iAdelic, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add]

omit [WeilData E] in
private lemma leviMatrix_mul_lAdelic (x : GL p (𝔸 E) × G E s₀) :
    (D.kAdelic * x.fst.val * D.kCoord + D.iAdelic * x.snd.adeleMatrix * D.iCoord +
      D.lAdelic * (x.fst⁻¹).valᴴ * D.lCoord) * D.lAdelic = D.lAdelic * (x.fst⁻¹).valᴴ := by
  simp only [Matrix.add_mul, Matrix.mul_assoc, D.kCoord_mul_lAdelic, D.iCoord_mul_lAdelic,
    D.lCoord_mul_lAdelic, Matrix.mul_one, Matrix.mul_zero, zero_add]

omit [WeilData E] in
private lemma levi_mem (x : GL p (𝔸 E) × G E s₀) :
    (D.kAdelic * x.fst.val * D.kCoord + D.iAdelic * x.snd.adeleMatrix * D.iCoord +
        D.lAdelic * (x.fst⁻¹).valᴴ * D.lCoord)ᴴ * stdForm E s *
      (D.kAdelic * x.fst.val * D.kCoord + D.iAdelic * x.snd.adeleMatrix * D.iCoord +
        D.lAdelic * (x.fst⁻¹).valᴴ * D.lCoord) = stdForm E s := by
  set M : Matrix n n (𝔸 E) :=
    D.kAdelic * x.fst.val * D.kCoord + D.iAdelic * x.snd.adeleMatrix * D.iCoord +
      D.lAdelic * (x.fst⁻¹).valᴴ * D.lCoord
  have hMtk : Mᴴ * (stdForm E s * D.kAdelic) = stdForm E s * D.kAdelic * x.fst⁻¹.val := by
    simp only [M, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.add_mul, Matrix.mul_assoc, D.conjTranspose_kAdelic_mul_stdForm_mul,
      D.conjTranspose_iAdelic_mul_stdForm_mul, D.conjTranspose_lAdelic_mul_stdForm_mul,
      D.lCoord_mul_kAdelic, D.iCoord_mul_kAdelic, D.kCoord_mul_kAdelic, D.conjTranspose_lCoord,
      Matrix.mul_zero, Matrix.mul_one, zero_add]
  have hMti : Mᴴ * (stdForm E s * D.iAdelic) =
      stdForm E s * D.iAdelic * (stdForm E s₀ * x.snd.adeleMatrixᴴ * stdForm E s₀) := by
    simp only [M, conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_assoc,
      D.conjTranspose_kAdelic_mul_stdForm_mul, D.conjTranspose_iAdelic_mul_stdForm_mul,
      D.conjTranspose_lAdelic_mul_stdForm_mul, D.lCoord_mul_iAdelic, D.iCoord_mul_iAdelic,
      D.kCoord_mul_iAdelic, D.conjTranspose_iCoord, Matrix.mul_zero, Matrix.mul_one, zero_add,
      add_zero]
  have hMtl : Mᴴ * (stdForm E s * D.lAdelic) = stdForm E s * D.lAdelic * x.fst.valᴴ := by
    simp only [M, conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_assoc,
      D.conjTranspose_kAdelic_mul_stdForm_mul, D.conjTranspose_iAdelic_mul_stdForm_mul,
      D.conjTranspose_lAdelic_mul_stdForm_mul, D.lCoord_mul_lAdelic, D.iCoord_mul_lAdelic,
      D.kCoord_mul_lAdelic, D.conjTranspose_kCoord, Matrix.mul_zero, Matrix.mul_one, add_zero]
  refine D.eq_of_mul_kAdelic_of_mul_iAdelic_of_mul_lAdelic ?_ ?_ ?_
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, D.leviMatrix_mul_kAdelic x,
      ← Matrix.mul_assoc (stdForm E s) D.kAdelic, ← Matrix.mul_assoc Mᴴ (stdForm E s * D.kAdelic),
      hMtk, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, D.leviMatrix_mul_iAdelic x,
      ← Matrix.mul_assoc (stdForm E s) D.iAdelic, ← Matrix.mul_assoc Mᴴ (stdForm E s * D.iAdelic),
      hMti, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc (stdForm E s₀),
      Matrix.mul_assoc (stdForm E s₀), x.snd.conjTranspose_adeleMatrix_mul_stdForm_mul_adeleMatrix,
      stdForm_mul_self, Matrix.mul_one]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, D.leviMatrix_mul_lAdelic x,
      ← Matrix.mul_assoc (stdForm E s) D.lAdelic, ← Matrix.mul_assoc Mᴴ (stdForm E s * D.lAdelic),
      hMtl, Matrix.mul_assoc, ← conjTranspose_mul, Units.inv_mul, conjTranspose_one, Matrix.mul_one]

omit [WeilData E] in
private lemma levi_map_mul (x y : GL p (𝔸 E) × G E s₀) :
    ofMatrix
        (D.kAdelic * (x * y).fst.val * D.kCoord + D.iAdelic * (x * y).snd.adeleMatrix * D.iCoord +
          D.lAdelic * ((x * y).fst⁻¹).valᴴ * D.lCoord) (D.levi_mem (x * y)) =
      ofMatrix
        (D.kAdelic * x.fst.val * D.kCoord + D.iAdelic * x.snd.adeleMatrix * D.iCoord +
          D.lAdelic * (x.fst⁻¹).valᴴ * D.lCoord) (D.levi_mem x) *
      ofMatrix
        (D.kAdelic * y.fst.val * D.kCoord + D.iAdelic * y.snd.adeleMatrix * D.iCoord +
          D.lAdelic * (y.fst⁻¹).valᴴ * D.lCoord) (D.levi_mem y) := by
  refine ext_adeleMatrix ?_
  rw [G.adeleMatrix_mul, adeleMatrix_ofMatrix, adeleMatrix_ofMatrix, adeleMatrix_ofMatrix]
  refine D.eq_of_mul_kAdelic_of_mul_iAdelic_of_mul_lAdelic ?_ ?_ ?_
  · rw [D.leviMatrix_mul_kAdelic, Matrix.mul_assoc, D.leviMatrix_mul_kAdelic, ← Matrix.mul_assoc,
      D.leviMatrix_mul_kAdelic, Matrix.mul_assoc, Prod.fst_mul, Units.val_mul]
  · rw [D.leviMatrix_mul_iAdelic, Matrix.mul_assoc, D.leviMatrix_mul_iAdelic, ← Matrix.mul_assoc,
      D.leviMatrix_mul_iAdelic, Matrix.mul_assoc, Prod.snd_mul, G.adeleMatrix_mul]
  · rw [D.leviMatrix_mul_lAdelic, Matrix.mul_assoc, D.leviMatrix_mul_lAdelic, ← Matrix.mul_assoc,
      D.leviMatrix_mul_lAdelic, Matrix.mul_assoc, Prod.fst_mul, _root_.mul_inv_rev, Units.val_mul,
      conjTranspose_mul]

/-- The Levi homomorphism `GL_p(𝔸) × G(V₀) → G(V)` of a splitting. The pair `(m, g₀)` goes to the
element that sends the frame `k` to `k m`, the embedded copy `ι` of `V₀` to `ι g₀` and the frame `l`
to `l (m⁻¹)ᴴ`; its matrix is `k m kCoord + ι g₀ iCoord + l (m⁻¹)ᴴ lCoord`. -/
@[local simp]
def levi : GL p (𝔸 E) × G E s₀ →* G E s :=
  MonoidHom.mk'
    (fun x ↦ ofMatrix
      (D.kAdelic * x.fst.val * D.kCoord + D.iAdelic * x.snd.adeleMatrix * D.iCoord +
        D.lAdelic * (x.fst⁻¹).valᴴ * D.lCoord) (by exact D.levi_mem x))
    (fun x y ↦ by exact D.levi_map_mul x y)

section

omit [WeilData E]

/-- The Levi element of `(a, g)` sends the adelic frame `l` to `l (a⁻¹)ᴴ`. -/
lemma levi_mul_lAdelic (a : GL p (𝔸 E)) (g : G E s₀) :
    (D.levi (a, g)).adeleMatrix * D.lAdelic = D.lAdelic * a⁻¹.valᴴ := by
  rw [levi, MonoidHom.mk'_apply, adeleMatrix_ofMatrix]
  exact D.leviMatrix_mul_lAdelic (a, g)

/-- The Levi element of `(a, g)` sends the embedded copy `ι` of `V₀` to `ι g`. -/
lemma levi_mul_iAdelic (a : GL p (𝔸 E)) (g : G E s₀) :
    (D.levi (a, g)).adeleMatrix * D.iAdelic = D.iAdelic * g.adeleMatrix := by
  rw [levi, MonoidHom.mk'_apply, adeleMatrix_ofMatrix]
  exact D.leviMatrix_mul_iAdelic (a, g)

/-- The Levi element of `(a, g)` acts on the adelic frame `k` by `a`. -/
lemma actsOnFrame_levi (a : GL p (𝔸 E)) (g : G E s₀) : D.ActsOnFrame (D.levi (a, g)) a.val := by
  rw [ActsOnFrame, levi, MonoidHom.mk'_apply, adeleMatrix_ofMatrix]
  exact D.leviMatrix_mul_kAdelic (a, g)

end

/-- Composition of splittings. From a splitting `D` of `V` over `V₀` with frames of `p` columns and
a splitting `D'` of `V₀` over `V₁` with frames of `q` columns, the splitting of `V` over `V₁` with
frames `(k, i k')` and `(l, i l')` and embedding `i i'`. -/
def comp [Fintype q] [DecidableEq q] (D' : V₀.Splitting V₁ q) : V.Splitting V₁ (p ⊕ q) := by
  -- The frames are `k := (k, i k')`, `l := (l, i l')` and `i := i i'`. Each Gram matrix splits
  -- into blocks, which reduce to the relations of `D` and of `D'`; they become visible by
  -- bracketing the products to the left, then to the right.
  use D.k.fromCols (D.i * D'.k), D.l.fromCols (D.i * D'.l), D.i * D'.i <;>
    simp +arith [D.card_eq, D'.card_eq, ← Matrix.mul_assoc,
      conjTranspose_fromCols_eq_fromRows_conjTranspose] <;>
    simp [Matrix.mul_assoc]

/-- The three frames `l`, `k`, `i` of a splitting, side by side in one matrix `M`, have the Gram
matrix of the orthogonal sum of hyperbolic space of rank `2 p` and `V₀`. -/
lemma gram_eq_hyperbolicSum :
    let M : Matrix n ((p ⊕ p) ⊕ n₀) E := (D.l.fromCols D.k).fromCols D.i
    Mᴴ * V.J * M = (hyperbolicSum p V₀).J := by
  -- Block by block, this is one of the relations `gram_ll`, `gram_lk`, ... of the splitting.
  aesop (add simp [conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.mul_assoc])

/-! ### The unipotent radical and the Levi decomposition -/

private lemma radicalZ_add_conjTranspose {R n₀ p : Type*} [CommRing R] [StarRing R]
    [Fintype n₀] {α β : R} (hα : α + α = 1) (hαs : star α = α) (hβs : star β = -β)
    {ε₀ : Matrix n₀ n₀ R} (hε₀ : ε₀ᴴ = ε₀) (c : Matrix n₀ p R) (b : Matrix p p R) :
    α • (β • (b + bᴴ) + cᴴ * ε₀ * c) + (α • (β • (b + bᴴ) + cᴴ * ε₀ * c))ᴴ = cᴴ * ε₀ * c := by
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul,
    conjTranspose_conjTranspose, hαs, hβs, hε₀, neg_smul, Matrix.mul_assoc]
  rw [← smul_add,
    show β • (b + bᴴ) + cᴴ * (ε₀ * c) + (-(β • (bᴴ + b)) + cᴴ * (ε₀ * c)) =
      cᴴ * (ε₀ * c) + cᴴ * (ε₀ * c) by rw [add_comm bᴴ b]; abel,
    smul_add, ← add_smul, hα, one_smul, ← Matrix.mul_assoc]

private lemma radicalZ_mul_eq {R n₀ p : Type*} [CommRing R] [StarRing R] [Fintype n₀]
    {α β γ : R} (hα : α + α = 1) (hβγ : β * γ = 1) (hγs : star γ = -γ)
    {ε₀ : Matrix n₀ n₀ R} (hε₀ : ε₀ᴴ = ε₀)
    (c c' : Matrix n₀ p R) (b b' : Matrix p p R) :
    α • (β • (b + bᴴ) + cᴴ * ε₀ * c) + cᴴ * ε₀ * c' + α • (β • (b' + b'ᴴ) + c'ᴴ * ε₀ * c') =
      α • (β • ((b + γ • cᴴ * ε₀ * c' + b') + (b + γ • cᴴ * ε₀ * c' + b')ᴴ) +
        (c + c')ᴴ * ε₀ * (c + c')) := by
  have h_cross : β • ((γ • cᴴ * ε₀ * c') + (γ • cᴴ * ε₀ * c')ᴴ) =
      cᴴ * ε₀ * c' - c'ᴴ * ε₀ * c := by
    simp only [Matrix.smul_mul, conjTranspose_smul, conjTranspose_mul,
      conjTranspose_conjTranspose, hε₀, hγs, neg_smul, smul_add, smul_neg, smul_smul, hβγ,
      one_smul, Matrix.mul_assoc, sub_eq_add_neg]
  have h_quad : (c + c')ᴴ * ε₀ * (c + c') =
      cᴴ * ε₀ * c + cᴴ * ε₀ * c' + c'ᴴ * ε₀ * c + c'ᴴ * ε₀ * c' := by
    simp only [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    abel
  have h_two : α • (cᴴ * ε₀ * c') + α • (cᴴ * ε₀ * c') = cᴴ * ε₀ * c' := by
    rw [← add_smul, hα, one_smul]
  rw [h_quad, conjTranspose_add, conjTranspose_add,
    show β • (b + γ • cᴴ * ε₀ * c' + b' + (bᴴ + (γ • cᴴ * ε₀ * c')ᴴ + b'ᴴ)) =
      β • (b + bᴴ) + β • (b' + b'ᴴ) + β • ((γ • cᴴ * ε₀ * c') + (γ • cᴴ * ε₀ * c')ᴴ) by
      simp only [smul_add]; abel,
    h_cross,
    show β • (b + bᴴ) + β • (b' + b'ᴴ) + (cᴴ * ε₀ * c' - c'ᴴ * ε₀ * c) +
        (cᴴ * ε₀ * c + cᴴ * ε₀ * c' + c'ᴴ * ε₀ * c + c'ᴴ * ε₀ * c') =
      (β • (b + bᴴ) + cᴴ * ε₀ * c) + (cᴴ * ε₀ * c' + cᴴ * ε₀ * c') +
        (β • (b' + b'ᴴ) + c'ᴴ * ε₀ * c') by abel]
  simp only [smul_add]
  conv_lhs => rw [← h_two]

private lemma radicalZ_skew_add_conjTranspose {R n₀ p : Type*} [CommRing R] [StarRing R]
    [Fintype n₀] {γ : R} (hγs : star γ = -γ) {ε₀ : Matrix n₀ n₀ R} (hε₀ : ε₀ᴴ = ε₀)
    (c : Matrix n₀ p R) :
    (γ • cᴴ * ε₀ * c) + (γ • cᴴ * ε₀ * c)ᴴ = 0 := by
  simp only [Matrix.smul_mul, conjTranspose_smul, conjTranspose_mul,
    conjTranspose_conjTranspose, hε₀, hγs, neg_smul, Matrix.mul_assoc, add_neg_cancel]

private lemma radicalZ_levi_comm_eq {R n₀ p : Type*} [CommRing R] [StarRing R]
    [Fintype n₀] [Fintype p] [DecidableEq p] {t₃ γ : R} (ht₃ : (4 : R) * t₃ = t₃ + 1)
    (hγs : star γ = -γ) {ε₀ : Matrix n₀ n₀ R} (hε₀ : ε₀ᴴ = ε₀)
    (c : Matrix n₀ p R) (b : Matrix p p R) :
    (1 + 1 : Matrix p p R) * (t₃ • b) * (1 + 1 : Matrix p p R)ᴴ +
      ((1 + 1 : Matrix p p R) * (t₃ • b) * (1 + 1 : Matrix p p R)ᴴ)ᴴ =
      (t₃ • b + γ • cᴴ * ε₀ * c + b) + (t₃ • b + γ • cᴴ * ε₀ * c + b)ᴴ := by
  have h_two : (1 + 1 : Matrix p p R) * (t₃ • b) * (1 + 1 : Matrix p p R)ᴴ =
      (4 : R) • (t₃ • b) := by
    simp only [conjTranspose_add, conjTranspose_one, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one]
    rw [show (4 : R) = 1 + 1 + (1 + 1) by norm_num, add_smul, add_smul, one_smul]
  have h_rhs : (t₃ • b + γ • cᴴ * ε₀ * c + b) + (t₃ • b + γ • cᴴ * ε₀ * c + b)ᴴ =
      (t₃ • b + b + (t₃ • b + b)ᴴ) + (γ • cᴴ * ε₀ * c + (γ • cᴴ * ε₀ * c)ᴴ) := by
    simp only [conjTranspose_add]
    abel
  rw [h_two, smul_smul, ht₃, add_smul, one_smul, h_rhs,
    radicalZ_skew_add_conjTranspose hγs hε₀ c, add_zero]

private lemma radicalZ_levi_decomp_k_part {R n n₀ p : Type*} [CommRing R] [StarRing R]
    [Fintype n] [Fintype n₀] [Fintype p] [DecidableEq p]
    {α β γ : R} (hα : α + α = 1) (hβγ : β * γ = 1) (hγs : star γ = -γ)
    (a : GL p R) (X : Matrix p n R) (Y : Matrix n₀ n R) (L : Matrix n p R) (ε₀ : Matrix n₀ n₀ R)
    (h_xl : Lᴴ * (Xᴴ * a⁻¹.valᴴ) = -(a⁻¹.val * (X * L)) - Lᴴ * (Yᴴ * (ε₀ * (Y * L)))) :
    α • (β • (-γ • X * L * a.valᴴ + (-γ • X * L * a.valᴴ)ᴴ) +
      (-Y * L * a.valᴴ)ᴴ * ε₀ * (-Y * L * a.valᴴ)) * a⁻¹.valᴴ = -(X * L) := by
  have ha_mul : a.valᴴ * a⁻¹.valᴴ = 1 := by
    rw [← conjTranspose_mul, Units.inv_mul, conjTranspose_one]
  have h_y : (-Y * L * a.valᴴ)ᴴ * ε₀ * (-Y * L * a.valᴴ) * a⁻¹.valᴴ =
      a.val * (Lᴴ * (Yᴴ * (ε₀ * (Y * L)))) := by
    simp only [Matrix.neg_mul, conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_neg, neg_neg, Matrix.mul_assoc, ha_mul, Matrix.mul_one]
  have h_b_conj : (-γ • X * L * a.valᴴ)ᴴ * a⁻¹.valᴴ = γ • (a.val * (Lᴴ * (Xᴴ * a⁻¹.valᴴ))) := by
    simp only [Matrix.neg_mul, conjTranspose_neg, Matrix.smul_mul, conjTranspose_smul,
      conjTranspose_mul, conjTranspose_conjTranspose, hγs, neg_smul, neg_neg, Matrix.mul_assoc]
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.add_mul, h_y, h_b_conj, h_xl,
    Matrix.mul_assoc (-γ • X * L), ha_mul, Matrix.mul_one]
  simp only [Matrix.neg_mul, Matrix.smul_mul, smul_add, smul_neg, smul_sub, smul_smul,
    mul_neg, hβγ, mul_one, neg_smul, Matrix.mul_sub, ← Matrix.mul_assoc a.val a⁻¹.val,
    Units.mul_inv, Matrix.one_mul]
  rw [show -(α • (X * L)) + (-(α • (X * L)) - α • (a.val * (Lᴴ * (Yᴴ * (ε₀ * (Y * L)))))) +
        α • (a.val * (Lᴴ * (Yᴴ * (ε₀ * (Y * L))))) =
      -(α • (X * L) + α • (X * L)) by abel,
    ← add_smul, hα, one_smul]

private lemma radicalZ_levi_conj_eq {R n n₀ p : Type*} [CommRing R] [StarRing R]
    [Fintype n] [Fintype n₀] [Fintype p] [DecidableEq p]
    (α β : R) (K : Matrix n p R) (a : GL p R) (g : Matrix n₀ n₀ R) (ε₀ : Matrix n₀ n₀ R)
    (hg : gᴴ * ε₀ * g = ε₀) (c : Matrix n₀ p R) (b : Matrix p p R) :
    K * a.val * (α • (β • (b + bᴴ) + cᴴ * ε₀ * c)) =
      K * (α • (β • (a.val * b * a.valᴴ + (a.val * b * a.valᴴ)ᴴ) +
        (g * c * a.valᴴ)ᴴ * ε₀ * (g * c * a.valᴴ))) * a⁻¹.valᴴ := by
  have ha : a.valᴴ * a⁻¹.valᴴ = 1 := by
    rw [← conjTranspose_mul, Units.inv_mul, conjTranspose_one]
  have hg' : gᴴ * (ε₀ * (g * c)) = ε₀ * c := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, ha, Matrix.mul_one, hg']

private lemma radicalElement_mem :
    (1 - D.iAdelic * c * D.lCoord + D.kAdelic * (cᴴ * stdForm E s₀) * D.iCoord -
        D.kAdelic * (toAdele (2⁻¹ : E) • (toAdele (j⁻¹ : E) • (b + bᴴ) + cᴴ * stdForm E s₀ * c)) *
          D.lCoord)ᴴ * stdForm E s *
      (1 - D.iAdelic * c * D.lCoord + D.kAdelic * (cᴴ * stdForm E s₀) * D.iCoord -
        D.kAdelic * (toAdele (2⁻¹ : E) • (toAdele (j⁻¹ : E) • (b + bᴴ) + cᴴ * stdForm E s₀ * c)) *
          D.lCoord) = stdForm E s := by
  -- The matrix preserves the form: verify `Mᴴ S M = S` on the three frames `k`, `i`, `l`.
  set Z : Matrix p p (𝔸 E) :=
    toAdele (2⁻¹ : E) • (toAdele (j⁻¹ : E) • (b + bᴴ) + cᴴ * stdForm E s₀ * c)
  set M : Matrix n n (𝔸 E) :=
    1 - D.iAdelic * c * D.lCoord + D.kAdelic * (cᴴ * stdForm E s₀) * D.iCoord -
      D.kAdelic * Z * D.lCoord
  have hZ : Z + Zᴴ = cᴴ * stdForm E s₀ * c :=
    radicalZ_add_conjTranspose (toAdele_half_add_half (E := E))
      (by rw [star_toAdele, star_inv₀, star_ofNat])
      (by rw [star_toAdele, star_inv₀, star_j, inv_neg, map_neg toAdele])
      conjTranspose_stdForm c b
  have hMk : M * D.kAdelic = D.kAdelic := by
    simp only [M, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
      D.lCoord_mul_kAdelic, D.iCoord_mul_kAdelic, Matrix.mul_zero, sub_zero, add_zero]
  have hMi : M * D.iAdelic = D.iAdelic + D.kAdelic * (cᴴ * stdForm E s₀) := by
    simp only [M, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
      D.lCoord_mul_iAdelic, D.iCoord_mul_iAdelic, Matrix.mul_zero, Matrix.mul_one, sub_zero]
  have hMl : M * D.lAdelic = D.lAdelic - D.iAdelic * c - D.kAdelic * Z := by
    simp only [M, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
      D.lCoord_mul_lAdelic, D.iCoord_mul_lAdelic, Matrix.mul_one, Matrix.mul_zero, add_zero]
  have hMtk : Mᴴ * (stdForm E s * D.kAdelic) = stdForm E s * D.kAdelic := by
    simp only [M, conjTranspose_sub, conjTranspose_add, conjTranspose_one, conjTranspose_mul,
      Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
      D.conjTranspose_kAdelic_mul_stdForm_mul, D.conjTranspose_iAdelic_mul_stdForm_mul,
      D.lCoord_mul_kAdelic, D.iCoord_mul_kAdelic, Matrix.mul_zero, sub_zero, add_zero]
  have hMti : Mᴴ * (stdForm E s * D.iAdelic) =
      stdForm E s * D.iAdelic - stdForm E s * (D.kAdelic * (cᴴ * stdForm E s₀)) := by
    simp only [M, conjTranspose_sub, conjTranspose_add, conjTranspose_one, conjTranspose_mul,
      Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
      D.conjTranspose_kAdelic_mul_stdForm_mul, D.conjTranspose_iAdelic_mul_stdForm_mul,
      D.lCoord_mul_iAdelic, D.iCoord_mul_iAdelic, D.conjTranspose_lCoord, Matrix.mul_zero,
      Matrix.mul_one, add_zero, sub_zero]
  have hMtl : Mᴴ * (stdForm E s * D.lAdelic) =
      stdForm E s * D.lAdelic + stdForm E s * (D.iAdelic * c) -
        stdForm E s * (D.kAdelic * Zᴴ) := by
    simp only [M, conjTranspose_sub, conjTranspose_add, conjTranspose_one, conjTranspose_mul,
      conjTranspose_conjTranspose, conjTranspose_stdForm, Matrix.sub_mul, Matrix.add_mul,
      Matrix.one_mul, Matrix.mul_assoc, D.conjTranspose_kAdelic_mul_stdForm_mul,
      D.conjTranspose_iAdelic_mul_stdForm_mul, D.lCoord_mul_lAdelic, D.iCoord_mul_lAdelic,
      D.conjTranspose_lCoord, D.conjTranspose_iCoord, stdForm_mul_stdForm_mul,
      Matrix.mul_zero, Matrix.mul_one, sub_zero]
  refine D.eq_of_mul_kAdelic_of_mul_iAdelic_of_mul_lAdelic ?_ ?_ ?_
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, hMk, hMtk]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, hMi, Matrix.mul_add, Matrix.mul_add, hMti,
      ← Matrix.mul_assoc (stdForm E s) D.kAdelic,
      ← Matrix.mul_assoc Mᴴ (stdForm E s * D.kAdelic), hMtk, Matrix.mul_assoc (stdForm E s),
      sub_add_cancel]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, hMl, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.mul_sub, hMtl,
      ← Matrix.mul_assoc (stdForm E s) D.iAdelic c,
      ← Matrix.mul_assoc Mᴴ (stdForm E s * D.iAdelic) c, hMti,
      ← Matrix.mul_assoc (stdForm E s) D.kAdelic Z,
      ← Matrix.mul_assoc Mᴴ (stdForm E s * D.kAdelic) Z, hMtk, Matrix.sub_mul,
      Matrix.mul_assoc (stdForm E s) D.iAdelic, Matrix.mul_assoc (stdForm E s) D.kAdelic,
      Matrix.mul_assoc (stdForm E s), Matrix.mul_assoc D.kAdelic]
    have h_cancel : stdForm E s * (D.kAdelic * Zᴴ) + stdForm E s * (D.kAdelic * Z) =
        stdForm E s * (D.kAdelic * (cᴴ * stdForm E s₀ * c)) := by
      rw [← Matrix.mul_add, ← Matrix.mul_add, add_comm Zᴴ Z, hZ]
    rw [show stdForm E s * D.lAdelic + stdForm E s * (D.iAdelic * c) -
          stdForm E s * (D.kAdelic * Zᴴ) -
          (stdForm E s * (D.iAdelic * c) -
            stdForm E s * (D.kAdelic * (cᴴ * stdForm E s₀ * c))) -
          stdForm E s * (D.kAdelic * Z) =
        stdForm E s * D.lAdelic + stdForm E s * (D.kAdelic * (cᴴ * stdForm E s₀ * c)) -
          (stdForm E s * (D.kAdelic * Zᴴ) + stdForm E s * (D.kAdelic * Z)) by abel,
      h_cancel, add_sub_cancel_right]

/-- The unipotent element of `G` with parameters an adelic `n₀ × p` matrix `c` and an adelic `p × p`
matrix `b`. It fixes the frame `k`, sends the embedded copy `ι` of `V₀` to `ι + k cᴴ ε₀` and
the frame `l` to `l − ι c − k (½ j⁻¹ (b + bᴴ) + ½ cᴴ ε₀ c)`, where `ε₀` is the standard form of `V₀`
and `j` the purely imaginary element of the Weil data. Only the hermitian part `z = ½ (b + bᴴ)` of
`b` enters: in the basis `(k, ι, l)` the matrix has the rows `(1, c*, −j⁻¹ z − ½ c* c)`,
`(0, 1, −c)`, `(0, 0, 1)`, with `c* = cᴴ ε₀` the adjoint of `c` for the form of `V₀`. -/
@[local simp]
def radicalElement : G E s :=
  ofMatrix
    (1 - D.iAdelic * c * D.lCoord + D.kAdelic * (cᴴ * stdForm E s₀) * D.iCoord -
      D.kAdelic * (toAdele (2⁻¹ : E) • (toAdele (j⁻¹ : E) • (b + bᴴ) + cᴴ * stdForm E s₀ * c)) *
        D.lCoord)
    (by exact D.radicalElement_mem c b)

/-- The unipotent element `radicalElement c b` depends continuously on the pair `(c, b)`. -/
@[fun_prop]
lemma continuous_radicalElement :
    Continuous fun q : Matrix n₀ p (𝔸 E) × Matrix p p (𝔸 E) ↦ D.radicalElement q.fst q.snd := by
  -- The matrix of `radicalElement c b` is a polynomial expression in the entries of `c` and `b` and
  -- their conjugates.
  simp only [G.continuous_iff, radicalElement, adeleMatrix_ofMatrix]
  have h_c : Continuous fun q : Matrix n₀ p (𝔸 E) × Matrix p p (𝔸 E) ↦ q.1 := continuous_fst
  have h_b : Continuous fun q : Matrix n₀ p (𝔸 E) × Matrix p p (𝔸 E) ↦ q.2 := continuous_snd
  have h_c_ct : Continuous fun q : Matrix n₀ p (𝔸 E) × Matrix p p (𝔸 E) ↦ q.1ᴴ :=
    continuous_pi fun i ↦ continuous_pi fun j ↦
      continuous_star.comp ((continuous_apply i).comp ((continuous_apply j).comp h_c))
  have h_b_ct : Continuous fun q : Matrix n₀ p (𝔸 E) × Matrix p p (𝔸 E) ↦ q.2ᴴ :=
    continuous_pi fun i ↦ continuous_pi fun j ↦
      continuous_star.comp ((continuous_apply i).comp ((continuous_apply j).comp h_b))
  have h_smul (a : 𝔸 E) {f : Matrix n₀ p (𝔸 E) × Matrix p p (𝔸 E) → Matrix p p (𝔸 E)}
      (hf : Continuous f) : Continuous fun q ↦ a • f q :=
    continuous_pi fun i ↦ continuous_pi fun j ↦
      continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp hf))
  have h1 : Continuous fun q : Matrix n₀ p (𝔸 E) × Matrix p p (𝔸 E) ↦
      1 - D.iAdelic * q.1 * D.lCoord :=
    continuous_const.sub ((continuous_const.matrix_mul h_c).matrix_mul continuous_const)
  have h2 : Continuous fun q : Matrix n₀ p (𝔸 E) × Matrix p p (𝔸 E) ↦
      D.kAdelic * (q.1ᴴ * stdForm E s₀) * D.iCoord :=
    (continuous_const.matrix_mul (h_c_ct.matrix_mul continuous_const)).matrix_mul continuous_const
  have h3 : Continuous fun q : Matrix n₀ p (𝔸 E) × Matrix p p (𝔸 E) ↦
      D.kAdelic * (toAdele (2⁻¹ : E) •
        (toAdele (j⁻¹ : E) • (q.2 + q.2ᴴ) + q.1ᴴ * stdForm E s₀ * q.1)) * D.lCoord :=
    (continuous_const.matrix_mul (h_smul _ ((h_smul _ (h_b.add h_b_ct)).add
      ((h_c_ct.matrix_mul continuous_const).matrix_mul h_c)))).matrix_mul continuous_const
  exact (h1.add h2).sub h3

/-- The unipotent element `radicalElement c b` fixes the adelic frame `k`. -/
lemma actsOnFrame_radicalElement : D.ActsOnFrame (D.radicalElement c b) 1 := by
  rw [ActsOnFrame, radicalElement, adeleMatrix_ofMatrix, Matrix.mul_one]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
    D.lCoord_mul_kAdelic, D.iCoord_mul_kAdelic, Matrix.mul_zero, sub_zero, add_zero]

/-- The unipotent element `radicalElement c b` sends the embedded copy `ι` of `V₀` to `ι + k cᴴ ε₀`,
where `ε₀` is the standard form of `V₀`. -/
lemma radicalElement_mul_iAdelic :
    (D.radicalElement c b).adeleMatrix * D.iAdelic =
      D.iAdelic + D.kAdelic * (cᴴ * stdForm E s₀) := by
  rw [radicalElement, adeleMatrix_ofMatrix]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
    D.lCoord_mul_iAdelic, D.iCoord_mul_iAdelic, Matrix.mul_zero, Matrix.mul_one, sub_zero]

private lemma radicalElement_mul_lAdelic :
    (D.radicalElement c b).adeleMatrix * D.lAdelic =
      D.lAdelic - D.iAdelic * c -
        D.kAdelic * (toAdele (2⁻¹ : E) •
          (toAdele (j⁻¹ : E) • (b + bᴴ) + cᴴ * stdForm E s₀ * c)) := by
  rw [radicalElement, adeleMatrix_ofMatrix]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
    D.lCoord_mul_lAdelic, D.iCoord_mul_lAdelic, Matrix.mul_one, Matrix.mul_zero, add_zero]

private lemma radicalElement_eq_of_add_conjTranspose_eq {c₁ c₂ : Matrix n₀ p (𝔸 E)}
    {b₁ b₂ : Matrix p p (𝔸 E)} (hc : c₁ = c₂) (hb : b₁ + b₁ᴴ = b₂ + b₂ᴴ) :
    D.radicalElement c₁ b₁ = D.radicalElement c₂ b₂ := by
  subst hc
  exact ext_adeleMatrix (by simp only [radicalElement, adeleMatrix_ofMatrix, hb])

/-- The Heisenberg group law of the unipotent elements: the parameters `c` add, and the parameters
`b` add with the extra term `j cᴴ ε₀ c'`, where `ε₀` is the standard form of `V₀` and `j` the purely
imaginary element of the Weil data. -/
@[local simp↓]
lemma radicalElement_mul (c' : Matrix n₀ p (𝔸 E)) (b' : Matrix p p (𝔸 E)) :
    D.radicalElement c b * D.radicalElement c' b' =
      D.radicalElement (c + c') (b + toAdele (j : E) • cᴴ * stdForm E s₀ * c' + b') := by
  refine ext_adeleMatrix ?_
  rw [G.adeleMatrix_mul]
  refine D.eq_of_mul_kAdelic_of_mul_iAdelic_of_mul_lAdelic ?_ ?_ ?_
  · rw [Matrix.mul_assoc, D.actsOnFrame_radicalElement, Matrix.mul_one,
      D.actsOnFrame_radicalElement, D.actsOnFrame_radicalElement]
  · rw [Matrix.mul_assoc, D.radicalElement_mul_iAdelic, Matrix.mul_add,
      D.radicalElement_mul_iAdelic, ← Matrix.mul_assoc (D.radicalElement c b).adeleMatrix D.kAdelic,
      D.actsOnFrame_radicalElement, Matrix.mul_one, D.radicalElement_mul_iAdelic,
      conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_assoc]
  · rw [Matrix.mul_assoc, D.radicalElement_mul_lAdelic, Matrix.mul_sub, Matrix.mul_sub,
      D.radicalElement_mul_lAdelic, ← Matrix.mul_assoc (D.radicalElement c b).adeleMatrix D.iAdelic,
      D.radicalElement_mul_iAdelic, ← Matrix.mul_assoc (D.radicalElement c b).adeleMatrix D.kAdelic,
      D.actsOnFrame_radicalElement, Matrix.mul_one, D.radicalElement_mul_lAdelic]
    have hj : toAdele (j⁻¹ : E) * toAdele (j : E) = 1 := by
      rw [← toAdele.map_mul, inv_mul_cancel₀ j_ne_zero, toAdele.map_one]
    have hjs : star (toAdele (j : E)) = -toAdele (j : E) := by
      rw [star_toAdele, star_j, map_neg toAdele]
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc D.kAdelic,
      ← radicalZ_mul_eq (toAdele_half_add_half (E := E)) hj hjs conjTranspose_stdForm c c' b b',
      Matrix.mul_add, Matrix.mul_add]
    abel

lemma radicalElement_inv : (D.radicalElement c b)⁻¹ = D.radicalElement (-c) (-b) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [radicalElement_mul, add_neg_cancel, add_comm b, add_assoc, add_neg_cancel, add_zero]
  have hjs : star (toAdele (j : E)) = -toAdele (j : E) := by
    rw [star_toAdele, star_j, map_neg toAdele]
  have h_skew : (toAdele (j : E) • cᴴ * stdForm E s₀ * (-c)) +
      (toAdele (j : E) • cᴴ * stdForm E s₀ * (-c))ᴴ = 0 := by
    rw [Matrix.mul_neg, conjTranspose_neg, ← neg_add,
      radicalZ_skew_add_conjTranspose hjs conjTranspose_stdForm c, neg_zero]
  exact (D.radicalElement_eq_of_add_conjTranspose_eq (b₂ := 0) rfl
      (by rw [h_skew, conjTranspose_zero, add_zero])).trans
    (ext_adeleMatrix (by simp only [radicalElement, adeleMatrix_ofMatrix, G.adeleMatrix_one,
      Matrix.mul_zero, conjTranspose_zero, Matrix.zero_mul, add_zero, smul_zero, sub_zero]))

/-- Conjugation by the Levi element of `(a, g)` sends `radicalElement c b` to
`radicalElement (g c aᴴ) (a b aᴴ)`. -/
lemma levi_conj_radicalElement (a : GL p (𝔸 E)) (g : G E s₀) :
    D.levi (a, g) * D.radicalElement c b =
      D.radicalElement (g.adeleMatrix * c * a.valᴴ) (a.val * b * a.valᴴ) * D.levi (a, g) := by
  refine ext_adeleMatrix ?_
  rw [G.adeleMatrix_mul, G.adeleMatrix_mul]
  have h_g : g.adeleMatrixᴴ * stdForm E s₀ * g.adeleMatrix = stdForm E s₀ :=
    g.conjTranspose_adeleMatrix_mul_stdForm_mul_adeleMatrix
  have h_a : a.valᴴ * a⁻¹.valᴴ = 1 := by
    rw [← conjTranspose_mul, Units.inv_mul, conjTranspose_one]
  refine D.eq_of_mul_kAdelic_of_mul_iAdelic_of_mul_lAdelic ?_ ?_ ?_
  · rw [Matrix.mul_assoc, D.actsOnFrame_radicalElement, Matrix.mul_one, D.actsOnFrame_levi,
      Matrix.mul_assoc, D.actsOnFrame_levi, ← Matrix.mul_assoc, D.actsOnFrame_radicalElement,
      Matrix.mul_one]
  · rw [Matrix.mul_assoc, D.radicalElement_mul_iAdelic, Matrix.mul_add, D.levi_mul_iAdelic,
      ← Matrix.mul_assoc (D.levi (a, g)).adeleMatrix D.kAdelic, D.actsOnFrame_levi,
      Matrix.mul_assoc (D.radicalElement _ _).adeleMatrix, D.levi_mul_iAdelic,
      ← Matrix.mul_assoc (D.radicalElement _ _).adeleMatrix D.iAdelic,
      D.radicalElement_mul_iAdelic, Matrix.add_mul]
    congr 1
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc g.adeleMatrixᴴ (stdForm E s₀), h_g]
  · rw [Matrix.mul_assoc, D.radicalElement_mul_lAdelic, Matrix.mul_sub, Matrix.mul_sub,
      D.levi_mul_lAdelic, ← Matrix.mul_assoc (D.levi (a, g)).adeleMatrix D.iAdelic,
      D.levi_mul_iAdelic, ← Matrix.mul_assoc (D.levi (a, g)).adeleMatrix D.kAdelic,
      D.actsOnFrame_levi, Matrix.mul_assoc (D.radicalElement _ _).adeleMatrix, D.levi_mul_lAdelic,
      ← Matrix.mul_assoc (D.radicalElement _ _).adeleMatrix D.lAdelic,
      D.radicalElement_mul_lAdelic, Matrix.sub_mul, Matrix.sub_mul]
    have h_i : D.iAdelic * (g.adeleMatrix * c * a.valᴴ) * a⁻¹.valᴴ =
        D.iAdelic * g.adeleMatrix * c := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, h_a, Matrix.mul_one,
        Matrix.mul_assoc]
    rw [h_i, radicalZ_levi_conj_eq (toAdele (2⁻¹ : E)) (toAdele (j⁻¹ : E)) D.kAdelic a
      g.adeleMatrix (stdForm E s₀) h_g c b]

/-- Every `radicalElement c b` is a commutator of a Levi element `m = levi (a, 1)` with a unipotent
element `u = radicalElement c b'`: `m * u = u * radicalElement c b * m`. -/
lemma exists_levi_mul_radicalElement_eq :
    ∃ (a : GL p (𝔸 E)) (b' : Matrix p p (𝔸 E)),
      D.levi (a, 1) * D.radicalElement c b' =
        D.radicalElement c b' * D.radicalElement c b * D.levi (a, 1) := by
  -- Conjugation by the scalar `2` sends `(c, b')` to `(2 c, 4 b')`, and
  -- `radicalElement c b' * radicalElement c b` is `radicalElement (2 c) (b' + b)` (the correction
  -- term of `radicalElement_mul` has hermitian part zero, as `star j = -j`); so take `b' = b / 3`.
  let two : GL p (𝔸 E) := .mkOfMulEqOne (1 + 1) (toAdele (2⁻¹ : E) • 1) <| by
    rw [Matrix.add_mul, Matrix.one_mul, ← add_smul, toAdele_half_add_half, one_smul]
  refine ⟨two, toAdele (3⁻¹ : E) • b, ?_⟩
  rw [levi_conj_radicalElement, radicalElement_mul]
  -- Both sides are a unipotent element times `levi (two, 1)`; compare the unipotent factors.
  refine congrArg (· * D.levi (two, 1)) (D.radicalElement_eq_of_add_conjTranspose_eq ?_ ?_)
  · rw [G.adeleMatrix_one, Matrix.one_mul]
    change c * (1 + 1)ᴴ = c + c
    simp only [conjTranspose_add, conjTranspose_one, Matrix.mul_add, Matrix.mul_one]
  · have h_three : (3 : 𝔸 E) * toAdele (3⁻¹ : E) = 1 := by
      rw [← map_ofNat toAdele 3, ← toAdele.map_mul, mul_inv_cancel₀ three_ne_zero, toAdele.map_one]
    have h_four : (4 : 𝔸 E) * toAdele (3⁻¹ : E) = toAdele (3⁻¹ : E) + 1 := by
      linear_combination h_three
    have hjs : star (toAdele (j : E)) = -toAdele (j : E) := by
      rw [star_toAdele, star_j, map_neg toAdele]
    exact radicalZ_levi_comm_eq h_four hjs conjTranspose_stdForm c b

/-- For two unipotent elements, the first with `c = 0`, the product adds the parameters `b`. -/
lemma radicalElement_zero_mul (b' : Matrix p p (𝔸 E)) :
    D.radicalElement 0 b * D.radicalElement c b' = D.radicalElement c (b + b') := by
  rw [radicalElement_mul, zero_add, conjTranspose_zero, smul_zero, Matrix.zero_mul,
    Matrix.zero_mul, add_zero]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Levi decomposition of the stabiliser of `range k`. Let `g` in `G` act on the adelic frame `k` by
an adelic `p × p` matrix `a`, that is `g k = k a`. Then `g = radicalElement c b * levi (t, g₀)` for
some parameters `c`, `b`, where `t` in `GL_p(𝔸)` has matrix `a` and `g₀` in `G(V₀)` has as matrix
the `V₀`-block `iCoord * g * iAdelic` of `g`. -/
lemma exists_eq_radicalElement_mul_levi (hk : D.ActsOnFrame g a) :
    ∃ (c : Matrix n₀ p (𝔸 E)) (b : Matrix p p (𝔸 E)) (t : GL p (𝔸 E)) (g₀ : G E s₀),
      g = D.radicalElement c b * D.levi (t, g₀) ∧
      t.val = a ∧
      g₀.adeleMatrix = D.iCoord * (g.adeleMatrix * D.iAdelic) := by
  -- Expand `g` in the frames `k`, `i`, `l`; the relations saying that `g` preserves the form then
  -- identify it with `radicalElement c b * levi (a, g₀)`.
  obtain ⟨a, rfl⟩ : ∃ u : GL p (𝔸 E), u.val = a := hk.isUnit
  obtain ⟨X, Y, hg⟩ : ∃ (X : Matrix p n (𝔸 E)) (Y : Matrix n₀ n (𝔸 E)),
      g.adeleMatrix = D.kAdelic * X + D.iAdelic * Y + D.lAdelic * (a.valᴴ⁻¹ * D.lCoord) := by
    refine ⟨D.kCoord * g.adeleMatrix, D.iCoord * g.adeleMatrix, ?_⟩
    -- Resolve the identity; the `l`-component of `g` is known from `lCoord_mul_adeleMatrix`.
    conv_lhs => rw [← g.adeleMatrix.one_mul, ← D.sum_frame_mul_coord_eq_one]
    simp [D.lCoord_mul_adeleMatrix hk, Matrix.add_mul, Matrix.mul_assoc, conjTranspose_nonsing_inv]
  -- `g` preserves the form; we use this on the columns `i` and `l`.
  have h_gi : g.adeleMatrix * D.iAdelic =
      D.kAdelic * (X * D.iAdelic) + D.iAdelic * (Y * D.iAdelic) := by
    rw [hg, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_assoc, D.lCoord_mul_iAdelic, Matrix.mul_zero, Matrix.mul_zero, add_zero]
  have h_gl : g.adeleMatrix * D.lAdelic =
      D.kAdelic * (X * D.lAdelic) + D.iAdelic * (Y * D.lAdelic) + D.lAdelic * a⁻¹.valᴴ := by
    rw [hg, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_assoc, D.lCoord_mul_lAdelic, Matrix.mul_one, Matrix.coe_units_inv,
      conjTranspose_nonsing_inv]
  have h_pres : g.adeleMatrixᴴ * (stdForm E s * g.adeleMatrix) = stdForm E s := by
    rw [← Matrix.mul_assoc, g.conjTranspose_adeleMatrix_mul_stdForm_mul_adeleMatrix]
  have h_gSk : g.adeleMatrixᴴ * (stdForm E s * D.kAdelic) =
      stdForm E s * (D.kAdelic * a.val⁻¹) := by
    rw [hg]
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose,
      conjTranspose_nonsing_inv, Matrix.add_mul, Matrix.mul_assoc,
      D.conjTranspose_kAdelic_mul_stdForm_mul, D.conjTranspose_iAdelic_mul_stdForm_mul,
      D.conjTranspose_lAdelic_mul_stdForm_mul, D.lCoord_mul_kAdelic, D.iCoord_mul_kAdelic,
      D.kCoord_mul_kAdelic, D.conjTranspose_lCoord, Matrix.mul_zero, Matrix.mul_one, zero_add]
  have h_gSi : g.adeleMatrixᴴ * (stdForm E s * D.iAdelic) = Yᴴ * stdForm E s₀ := by
    rw [hg]
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose,
      conjTranspose_nonsing_inv, Matrix.add_mul, Matrix.mul_assoc,
      D.conjTranspose_kAdelic_mul_stdForm_mul, D.conjTranspose_iAdelic_mul_stdForm_mul,
      D.conjTranspose_lAdelic_mul_stdForm_mul, D.lCoord_mul_iAdelic, D.iCoord_mul_iAdelic,
      D.kCoord_mul_iAdelic, Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero]
  have h_gSl : g.adeleMatrixᴴ * (stdForm E s * D.lAdelic) = Xᴴ := by
    rw [hg]
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose,
      conjTranspose_nonsing_inv, Matrix.add_mul, Matrix.mul_assoc,
      D.conjTranspose_kAdelic_mul_stdForm_mul, D.conjTranspose_iAdelic_mul_stdForm_mul,
      D.conjTranspose_lAdelic_mul_stdForm_mul, D.lCoord_mul_lAdelic, D.iCoord_mul_lAdelic,
      D.kCoord_mul_lAdelic, Matrix.mul_zero, Matrix.mul_one, add_zero]
  have h_form_i : Yᴴ * (stdForm E s₀ * (Y * D.iAdelic)) =
      stdForm E s * D.iAdelic - stdForm E s * (D.kAdelic * (a.val⁻¹ * (X * D.iAdelic))) := by
    have h := congrArg (· * D.iAdelic) h_pres
    rw [Matrix.mul_assoc, Matrix.mul_assoc, h_gi, Matrix.mul_add, Matrix.mul_add,
      ← Matrix.mul_assoc (stdForm E s) D.kAdelic, ← Matrix.mul_assoc g.adeleMatrixᴴ (stdForm E s * D.kAdelic),
      h_gSk, ← Matrix.mul_assoc (stdForm E s) D.iAdelic,
      ← Matrix.mul_assoc g.adeleMatrixᴴ (stdForm E s * D.iAdelic), h_gSi,
      Matrix.mul_assoc (stdForm E s), Matrix.mul_assoc D.kAdelic, Matrix.mul_assoc Yᴴ] at h
    exact eq_sub_of_add_eq' h
  have h_form_l : Xᴴ * a.valᴴ⁻¹ = stdForm E s * D.lAdelic -
      (stdForm E s * (D.kAdelic * (a.val⁻¹ * (X * D.lAdelic))) +
        Yᴴ * (stdForm E s₀ * (Y * D.lAdelic))) := by
    have h := congrArg (· * D.lAdelic) h_pres
    rw [Matrix.mul_assoc, Matrix.mul_assoc, h_gl, Matrix.mul_add, Matrix.mul_add,
      Matrix.mul_add, Matrix.mul_add,
      ← Matrix.mul_assoc (stdForm E s) D.kAdelic, ← Matrix.mul_assoc g.adeleMatrixᴴ (stdForm E s * D.kAdelic),
      h_gSk, ← Matrix.mul_assoc (stdForm E s) D.iAdelic,
      ← Matrix.mul_assoc g.adeleMatrixᴴ (stdForm E s * D.iAdelic), h_gSi,
      ← Matrix.mul_assoc (stdForm E s) D.lAdelic,
      ← Matrix.mul_assoc g.adeleMatrixᴴ (stdForm E s * D.lAdelic), h_gSl,
      Matrix.mul_assoc (stdForm E s), Matrix.mul_assoc D.kAdelic, Matrix.mul_assoc Yᴴ,
      Matrix.coe_units_inv, conjTranspose_nonsing_inv] at h
    exact eq_sub_of_add_eq' h
  let g₀ : G E s₀ :=
    ofMatrix (Y * D.iAdelic) (by
      rw [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, h_form_i, Matrix.mul_sub,
        D.conjTranspose_iAdelic_mul_stdForm_mul, D.iCoord_mul_iAdelic, Matrix.mul_one,
        D.conjTranspose_iAdelic_mul_stdForm_mul, D.iCoord_mul_kAdelic_mul, Matrix.mul_zero,
        sub_zero])
  refine ⟨-Y * D.lAdelic * a.valᴴ, -toAdele (j : E) • X * D.lAdelic * a.valᴴ, a, g₀,
    ext_adeleMatrix ?_, rfl, ?_⟩
  · -- Compare both sides on the frames `k`, `i` and `l`. On each frame the Levi factor acts
    -- first, by `actsOnFrame_levi`, `levi_mul_iAdelic` and `levi_mul_lAdelic`.
    rw [G.adeleMatrix_mul]
    refine D.eq_of_mul_kAdelic_of_mul_iAdelic_of_mul_lAdelic ?_ ?_ ?_
    · -- On `k` both act by `a`.
      rw [Matrix.mul_assoc, D.actsOnFrame_levi, ← Matrix.mul_assoc, D.actsOnFrame_radicalElement,
        Matrix.mul_one]
      exact hk
    · -- On `i`: by `h_form_i`, the `k`-part of the right side is `X i`, as on the left.
      rw [Matrix.mul_assoc, D.levi_mul_iAdelic, ← Matrix.mul_assoc, D.radicalElement_mul_iAdelic,
        h_gi, Matrix.add_mul, Matrix.mul_assoc D.kAdelic]
      have h_ik : (-Y * D.lAdelic * a.valᴴ)ᴴ * stdForm E s₀ * g₀.adeleMatrix = X * D.iAdelic := by
        simp only [g₀, adeleMatrix_ofMatrix, Matrix.neg_mul, conjTranspose_neg, conjTranspose_mul,
          conjTranspose_conjTranspose, Matrix.mul_neg, Matrix.mul_assoc, h_form_i, Matrix.mul_sub,
          D.conjTranspose_lAdelic_mul_stdForm_mul, D.kCoord_mul_iAdelic, D.kCoord_mul_kAdelic_mul,
          zero_sub, neg_neg, ← Matrix.coe_units_inv, ← Matrix.mul_assoc a.val a⁻¹.val,
          Units.mul_inv, Matrix.one_mul]
      rw [h_ik, add_comm]
      rfl
    · -- On `l`: `h_form_l` removes `Xᴴ`, which enters the right side through `bᴴ`.
      rw [Matrix.mul_assoc, D.levi_mul_lAdelic, ← Matrix.mul_assoc, D.radicalElement_mul_lAdelic,
        Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc D.iAdelic, Matrix.mul_assoc D.kAdelic]
      have ha_mul : a.valᴴ * a⁻¹.valᴴ = 1 := by
        rw [← conjTranspose_mul, Units.inv_mul, conjTranspose_one]
      have hj : toAdele (j⁻¹ : E) * toAdele (j : E) = 1 := by
        rw [← toAdele.map_mul, inv_mul_cancel₀ j_ne_zero, toAdele.map_one]
      have hjs : star (toAdele (j : E)) = -toAdele (j : E) := by
        rw [star_toAdele, star_j, map_neg toAdele]
      have h_i_part : -Y * D.lAdelic * a.valᴴ * a⁻¹.valᴴ = -(Y * D.lAdelic) := by
        rw [Matrix.mul_assoc, ha_mul, Matrix.mul_one, Matrix.neg_mul]
      have h_xl : D.lAdelicᴴ * (Xᴴ * a⁻¹.valᴴ) =
          -(a⁻¹.val * (X * D.lAdelic)) - D.lAdelicᴴ * (Yᴴ * (stdForm E s₀ * (Y * D.lAdelic))) := by
        rw [Matrix.coe_units_inv, conjTranspose_nonsing_inv, h_form_l, Matrix.mul_sub,
          Matrix.mul_add, D.conjTranspose_lAdelic_mul_stdForm_mul, D.kCoord_mul_lAdelic, zero_sub,
          D.conjTranspose_lAdelic_mul_stdForm_mul, D.kCoord_mul_kAdelic_mul, neg_add, sub_eq_add_neg]
      have h_k_part := radicalZ_levi_decomp_k_part (toAdele_half_add_half (E := E)) hj hjs
        a X Y D.lAdelic (stdForm E s₀) h_xl
      rw [h_gl, h_i_part, h_k_part, Matrix.mul_neg, Matrix.mul_neg, sub_neg_eq_add,
        sub_neg_eq_add]
      abel
  · -- The matrix of `g₀` is the `V₀`-block of `g`.
    rw [h_gi, Matrix.mul_add, D.iCoord_mul_kAdelic_mul, D.iCoord_mul_iAdelic_mul, zero_add]
    rfl

/-- The unipotent radical of the stabiliser of `A = range k` consists of the `radicalElement c b`:
an element `g` of the adelic unitary group of `V` is of this form exactly when it fixes the frame
`k` and acts as the identity on `A^⊥ / A`, that is, its `V₀`-block `iCoord * g * iAdelic` is `1`. -/
lemma exists_eq_radicalElement_iff :
    (∃ (c : Matrix n₀ p (𝔸 E)) (b : Matrix p p (𝔸 E)), g = D.radicalElement c b) ↔
      D.ActsOnFrame g 1 ∧ D.iCoord * (g.adeleMatrix * D.iAdelic) = 1 := by
  constructor
  · rintro ⟨c, b, rfl⟩
    exact ⟨D.actsOnFrame_radicalElement c b, by
      simp [↓radicalElement_mul_iAdelic, Matrix.mul_add]⟩
  · -- In the Levi decomposition of `g` both components of the Levi factor are `1`.
    rintro ⟨hk, hi⟩
    obtain ⟨c, b, t, g₀, hg, ht, hg₀⟩ := D.exists_eq_radicalElement_mul_levi hk
    obtain rfl : t = 1 := Units.ext ht
    obtain rfl : g₀ = 1 := ext_adeleMatrix (by rw [hg₀, hi, G.adeleMatrix_one])
    exact ⟨c, b, by rw [hg, Prod.mk_one_one, map_one, mul_one]⟩

/-! ### The law of the mixed model, and adapted points -/

/-- The law of a mixed Schrödinger model, for maps `T x : 𝒮 V → 𝒮 V₀` with `x` in `𝔸^p`. Write
`y = l a + ι w + k b`, so `a = lCoord y`, `w = iCoord y`, `b = kCoord y`. Then
`T x (ϱ y f) = β (2 x + a) b • ϱ w (T (x + a) f)`, with `β` the bicharacter of
`adelicHeisenberg E 1`: the `l`-part translates `x`, the `k`-part multiplies by a character, and the
`V₀`-part acts on the values. Here `𝒮 V` is the space of the Schrödinger model of `V`, and `V.ϱ y`
is the operator on it of the adelic vector `y`. In the code `2 x + a` is written `x + (x + a)`. -/
abbrev IsMixedLaw (T : (p → 𝔸 E) → 𝒮 V →L[ℂ] 𝒮 V₀) : Prop :=
  ∀ (x : p → 𝔸 E) (y : n → 𝔸 E) (f : 𝒮 V),
    T x (V.ϱ y f) =
      -- `x + (x + a)` is the sum of the old and the new argument of `T`, where `a = D.lCoord *ᵥ y`
      (adelicHeisenberg E 1).β (x + (x + D.lCoord *ᵥ y)) (D.kCoord *ᵥ y) •
        V₀.ϱ (D.iCoord *ᵥ y) (T (x + D.lCoord *ᵥ y) f)

variable {D} in
/-- If the family `T` obeys the law of a mixed model, then translating by a vector `l c` along the
isotropic frame `l` of the splitting shifts the argument of `T` by `c`. -/
lemma IsMixedLaw.apply_rho_lAdelic_mulVec {T : (p → 𝔸 E) → 𝒮 V →L[ℂ] 𝒮 V₀} (hT : D.IsMixedLaw T)
    (x c : p → 𝔸 E) (f : 𝒮 V) : T x (V.ϱ (D.lAdelic *ᵥ c) f) = T (x + c) f := by
  -- The `k`- and `V₀`-coordinates of `l c` vanish and its `l`-coordinate is `c`.
  simp [hT x, mulVec_mulVec]

variable (g : G E s) (t : GL p (𝔸 E))

/-- For `g` in `G` and `t` in `GL_p(𝔸)`, the adelic matrix `g⁻¹ (l (t⁻¹)ᴴ, k t, ι)`, where `l`, `k`,
`ι` are `D.lAdelic`, `D.kAdelic`, `D.iAdelic`, with three column blocks. -/
def frameAt : Matrix n ((p ⊕ p) ⊕ n₀) (𝔸 E) :=
  g⁻¹.adeleMatrix * ((D.lAdelic * t⁻¹.valᴴ).fromCols (D.kAdelic * t.val)).fromCols D.iAdelic

omit [WeilData E] in
/-- The Gram matrix of `frameAt g t` for the standard form: the hyperbolic block `(0, 1; 1, 0)` for
`l` and `k`, and the standard form of `V₀`. -/
lemma gram_frameAt :
    (D.frameAt g t)ᴴ * stdForm E s * D.frameAt g t =
      fromBlocks (fromBlocks 0 1 1 0) 0 0 (stdForm E s₀) := by
  -- `g⁻¹` preserves the form, so only the relations between `k`, `l` and `i` are left.
  refine (U.gram_invariant ..).trans ?_
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose,
    conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.mul_assoc,
    mul_fromCols (stdForm E s), mul_fromCols (stdForm E s),
    fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul, mul_fromCols]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
    D.conjTranspose_kAdelic_mul_stdForm_mul, D.conjTranspose_lAdelic_mul_stdForm_mul,
    D.conjTranspose_iAdelic_mul_stdForm_mul, D.kCoord_mul_kAdelic_mul, D.kCoord_mul_lAdelic_mul,
    D.kCoord_mul_iAdelic, D.lCoord_mul_kAdelic_mul, D.lCoord_mul_lAdelic_mul, D.lCoord_mul_iAdelic,
    D.iCoord_mul_kAdelic_mul, D.iCoord_mul_lAdelic_mul, D.iCoord_mul_iAdelic,
    Matrix.mul_zero, Matrix.mul_one, fromRows_zero, fromCols_zero]
  rw [Units.inv_mul, ← conjTranspose_mul, Units.inv_mul, conjTranspose_one]

/-- An element `g` of `G` is adapted to `t` in `GL_p(𝔸)` when the matrix `g⁻¹ (l (t⁻¹)ᴴ, k t, ι)`
has orthonormal columns at every infinite place and integral finite entries. -/
def IsAdapted : Prop := IsOrthoIntegral (D.frameAt g t)

/-- Adapted points exist. Let `D` be a Witt decomposition `V = (l E^p ⊕ k E^p) ⊥ i V₀`, where `E` is
a CM field with Weil data, and let `t` be in `GL_p(𝔸)`. Then there are `γ` in `G` and a bijection
`e : (p ⊕ p) ⊕ n₀ ≃ n` of index sets such that: `γ` is adapted to `t` (`γ⁻¹ (l (t⁻¹)ᴴ, k t, i)`,
where `l`, `k`, `i` are the adelic frames `D.lAdelic`, `D.kAdelic`, `D.iAdelic`, has orthonormal
columns at every infinite place and integral finite entries); the signs `s` of `V` reordered by `e`
are `hyperbolicSigns p` followed by `s₀`; and the adelic matrix of `γ` with columns reordered by `e`
equals `((l (t⁻¹)ᴴ, k t) x, i)` (that is, `D.frameAt 1 t` times `x ⊕ 1`), with `x` the adelic frame
of `hyperbolicSpace E p`. -/
lemma exists_isAdapted_and_frame_eq :
    ∃ γ : G E s, D.IsAdapted γ t ∧
      ∃ e : (p ⊕ p) ⊕ n₀ ≃ n, s ∘ e = hyperbolicSigns p ⊕ᵥ s₀ ∧
        D.frameAt 1 t * fromBlocks (o := n₀) (hyperbolicSpace E p).x.val 0 0 1 =
          γ.adeleMatrix.submatrix id e := by
  -- The columns `m = ((l (t⁻¹)ᴴ, k t) x, i)`, with `x` the frame of `hyperbolicSpace E p`, have the
  -- Gram matrix of the signs `hyperbolicSigns p ⊕ᵥ s₀`. Sylvester's law of inertia reorders them by
  -- a bijection `e` under which these signs become those of `V`; the reordered `m` is then the
  -- matrix of `γ`.
  let m : Matrix n ((p ⊕ p) ⊕ n₀) (𝔸 E) :=
    D.frameAt 1 t * fromBlocks (hyperbolicSpace E p).x.val 0 0 (1 : Matrix n₀ n₀ (𝔸 E))
  have h_gram : mᴴ * stdForm E s * m = stdForm E (hyperbolicSigns p ⊕ᵥ s₀) := by
    -- The Gram matrix of `frameAt 1 t` is the hyperbolic block plus the standard form of `V₀`,
    -- and the frame `x` of hyperbolic space carries the hyperbolic block to its standard form.
    rw [gram_mul, gram_frameAt]
    simp [← stdForm_sum, ← (hyperbolicSpace E p).gram_point, fromBlocks_conjTranspose,
      fromBlocks_multiply, fromBlocks_map]
  have σ : n ≃ (p ⊕ p) ⊕ n₀ := equivOfCardEq (by simp +arith [D.card_eq])
  let w : InfinitePlace E := Classical.ofNonempty
  have h_gram_w : (m.map (evalInf w))ᴴ * signMatrix s * m.map (evalInf w) =
      signMatrix (hyperbolicSigns p ⊕ᵥ s₀) := by
    simpa [Matrix.map_mul, stdForm, signMatrix, ← conjTranspose_map (evalInf w) (fun _ ↦ rfl)]
      using congrArg (·.map (evalInf w)) h_gram
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm n, ∀ i : n, s (τ i) = (hyperbolicSigns p ⊕ᵥ s₀) (σ i) :=
    sylvester_law_of_inertia (h := (m.map (evalInf w)).submatrix id σ) <| by
      simpa [signMatrix, comp_def, submatrix_mul _ _ σ id _ bijective_id]
        using congrArg (·.submatrix σ σ) h_gram_w
  let e : (p ⊕ p) ⊕ n₀ ≃ n := σ.symm.trans τ
  have h_sign : s ∘ e = hyperbolicSigns p ⊕ᵥ s₀ := funext fun i ↦ by simp [e, hτ]
  have h_form : (m.reindex 1 e)ᴴ * stdForm E s * m.reindex 1 e = stdForm E s := by
    -- Reorder the Gram matrix by `e`; by `h_sign` the result is the standard form of `s`.
    refine (congrArg (Matrix.reindex e e) h_gram).trans ?_
    simp [← h_sign, stdForm, submatrix_diagonal_equiv, Function.comp_def]
  let γ : G E s := ofMatrix (m.reindex 1 e) h_form
  have hγ : m = γ.adeleMatrix.submatrix id e := by simp [γ, Equiv.Perm.one_def]
  -- `frameAt γ t` is `x⁻¹ ⊕ 1` with its rows reordered by `e`.
  have h_frame : D.frameAt γ t = (1 : Matrix n n (𝔸 E)).submatrix id e *
      fromBlocks (hyperbolicSpace E p).x⁻¹.val 0 0 (1 : Matrix n₀ n₀ (𝔸 E)) := by
    have h_cancel : γ⁻¹.adeleMatrix * m = (1 : Matrix n n (𝔸 E)).submatrix id e := by
      rw [hγ, ← G.adeleMatrix_one (s := s), ← inv_mul_cancel γ, G.adeleMatrix_mul,
        submatrix_mul _ _ id id e bijective_id, submatrix_id_id]
    rw [← h_cancel]
    simp [frameAt, m, fromCols_mul_fromBlocks, Matrix.mul_assoc]
  refine ⟨γ, ?_, e, h_sign, hγ⟩
  exact .of_eq_submatrix_mul .one e
    (isOrthoIntegral_hyperbolicSpace_x_inv.block_diag .one) h_frame e.injective

/-! ### Rational elements -/

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
omit [WeilData E] in
/-- The Levi element of a rational matrix `a` in `GL_p(E)` and a rational point `g₀` of `V₀` is a
rational point of `V`. -/
lemma levi_mem_Gamma (a : GL p E) {g₀ : G E s₀} (hg₀ : g₀ ∈ V₀.Γ) :
    D.levi (GeneralLinearGroup.map toAdele a, g₀) ∈ V.Γ := by
  obtain ⟨γ, rfl⟩ := hg₀
  -- In the rational coordinates of V the Levi element is a matrix over E (the frames cancel).
  have h_rat : V.x.val * (D.levi (.map toAdele a, V₀.ratEmbed γ)).adeleMatrix * V.x⁻¹.val =
      (D.k * a.val * D.lᴴ * V.J + D.i * γ.val.val * V₀.J⁻¹ * D.iᴴ * V.J +
        D.l * a⁻¹.valᴴ * D.kᴴ * V.J).map toAdele := by
    have h_cancel (M : Matrix n₀ n (𝔸 E)) : V₀.x.val * (V₀.x⁻¹.val * M) = M := by simp
    -- `-coe_units_inv` keeps `x₀⁻¹` a unit, so that `h_cancel` cancels it against `x₀`.
    simp [adeleMatrix_ratEmbed, ← map_inv, map_J, map_J_inv, Matrix.map_add, -coe_units_inv,
      kAdelic, lAdelic, iAdelic, kCoord, lCoord, iCoord, ratMap, Matrix.mul_assoc, Matrix.mul_add,
      Matrix.add_mul, h_cancel]
  exact V.mem_Gamma_iff_range.2 (mem_ratMatrices.1 ⟨_, h_rat.symm⟩)

private lemma mul_triple_assoc {R a b c d e : Type*} [Semiring R]
    [Fintype b] [Fintype c] [Fintype d]
    (X : Matrix a b R) (A : Matrix b c R) (B : Matrix c d R) (C : Matrix d b R) (Y : Matrix b e R) :
    X * (A * B * C) * Y = (X * A) * (B * (C * Y)) := by
  simp only [Matrix.mul_assoc]

/-- The unipotent element `radicalElement (x₀⁻¹ c) b`, for a matrix `c` over `E`, `x₀` the adelic
frame of `V₀` and `b` an adelic matrix with entries in `E` (hypothesis `hb`), lies in the rational
group `Γ` of `V`. -/
lemma radicalElement_mem_Gamma (c : Matrix n₀ p E) {b : Matrix p p (𝔸 E)}
    (hb : b ∈ ratMatrices E p p) : D.radicalElement (V₀.x⁻¹.val * c.map toAdele) b ∈ V.Γ := by
  obtain ⟨b₀, rfl⟩ : ∃ b₀ : Matrix p p E, b₀.map toAdele = b := hb
  -- In the rational coordinates of V the unipotent element is a matrix over E: the adelic frames
  -- cancel or combine with the standard forms into J and J₀.
  have h_rat : V.x.val *
      (D.radicalElement (V₀.x⁻¹.val * c.map toAdele) (b₀.map toAdele)).adeleMatrix * V.x⁻¹.val =
      (1 - D.i * c * D.kᴴ * V.J + D.k * cᴴ * D.iᴴ * V.J - D.k *
        ((2⁻¹ : E) • ((j : E)⁻¹ • (b₀ + b₀ᴴ) + cᴴ * V₀.J * c)) * D.kᴴ * V.J).map toAdele := by
    have h_lCoord : D.lCoord * V.x⁻¹.val = (D.kᴴ * V.J).map toAdele := by
      simp [lCoord, kAdelic, map_J, Matrix.mul_assoc]
    have h_iCoord : D.iCoord * V.x⁻¹.val = stdForm E s₀ * V₀.x.valᴴ * (D.iᴴ * V.J).map toAdele := by
      simp [iCoord, iAdelic, ratMap, map_J, Matrix.mul_assoc]
    have h_iAdelic : V.x.val * D.iAdelic = D.i.map toAdele * V₀.x.val := by
      simp [iAdelic, ratMap, Matrix.mul_assoc]
    have h_kAdelic : V.x.val * D.kAdelic = D.k.map toAdele := by
      simp [kAdelic]
    have h_c_gram : (V₀.x⁻¹.val * c.map toAdele)ᴴ * stdForm E s₀ * (V₀.x⁻¹.val * c.map toAdele) =
        (cᴴ * V₀.J * c).map toAdele :=
      V₀.gram_at_point_eq_map c c
    rw [radicalElement, adeleMatrix_ofMatrix]
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_one]
    have h1 : V.x.val * V.x⁻¹.val = (1 : Matrix n n E).map toAdele := by
      rw [Units.mul_inv, Matrix.map_one toAdele toAdele.map_zero toAdele.map_one]
    have h2 : V.x.val * (D.iAdelic * (V₀.x⁻¹.val * c.map toAdele) * D.lCoord) * V.x⁻¹.val =
        (D.i * c * D.kᴴ * V.J).map toAdele := by
      rw [mul_triple_assoc, h_iAdelic, h_lCoord, Matrix.mul_assoc (D.i.map toAdele),
        ← Matrix.mul_assoc V₀.x.val, ← Matrix.mul_assoc V₀.x.val, Units.mul_inv, Matrix.one_mul,
        ← Matrix.map_mul, ← Matrix.map_mul]
      simp only [Matrix.mul_assoc]
    have h3 : V.x.val * (D.kAdelic * ((V₀.x⁻¹.val * c.map toAdele)ᴴ * stdForm E s₀) * D.iCoord) *
          V.x⁻¹.val = (D.k * cᴴ * D.iᴴ * V.J).map toAdele := by
      rw [mul_triple_assoc, h_kAdelic, h_iCoord, conjTranspose_mul]
      simp only [Matrix.mul_assoc, stdForm_mul_stdForm_mul]
      rw [← Matrix.mul_assoc (V₀.x⁻¹.val)ᴴ (V₀.x.val)ᴴ, ← conjTranspose_mul, Units.mul_inv,
        conjTranspose_one, Matrix.one_mul,
        ← conjTranspose_map toAdele (fun _ ↦ (star_toAdele _).symm),
        ← Matrix.map_mul, ← Matrix.map_mul]
    have h4 : V.x.val * (D.kAdelic * (toAdele (2⁻¹ : E) •
          (toAdele (j⁻¹ : E) • (b₀.map toAdele + (b₀.map toAdele)ᴴ) +
            (V₀.x⁻¹.val * c.map toAdele)ᴴ * stdForm E s₀ * (V₀.x⁻¹.val * c.map toAdele))) *
          D.lCoord) * V.x⁻¹.val =
        (D.k * ((2⁻¹ : E) • ((j : E)⁻¹ • (b₀ + b₀ᴴ) + cᴴ * V₀.J * c)) * D.kᴴ * V.J).map toAdele := by
      have h_mid : toAdele (2⁻¹ : E) •
            (toAdele (j⁻¹ : E) • (b₀.map toAdele + b₀ᴴ.map toAdele) +
              (cᴴ * V₀.J * c).map toAdele) =
          ((2⁻¹ : E) • ((j : E)⁻¹ • (b₀ + b₀ᴴ) + cᴴ * V₀.J * c)).map toAdele := by
        refine Matrix.ext fun i k ↦ ?_
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.map_apply, smul_eq_mul, map_mul,
          map_add]
      rw [mul_triple_assoc, h_kAdelic, h_lCoord, h_c_gram,
        ← conjTranspose_map toAdele (fun _ ↦ (star_toAdele _).symm), h_mid,
        ← Matrix.map_mul, ← Matrix.map_mul]
      simp only [Matrix.mul_assoc]
    rw [h1, h2, h3, h4]
    refine Matrix.ext fun i k ↦ ?_
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.map_apply, map_sub, map_add]
  exact V.mem_Gamma_iff_range.2 (mem_ratMatrices.1 ⟨_, h_rat.symm⟩)

/-- The rational points of the unipotent radical are cocompact. For a splitting `D` of `V` over
`V₀` along an isotropic subspace of any rank, there is a compact set `K` such that every element
`D.radicalElement c b` of the radical is moved into `K` by left multiplication with some
`D.radicalElement y z` that lies in the group `V.Γ` of rational points. -/
lemma exists_isCompact_rat_mul_radicalElement_mem (D : V.Splitting V₀ p) :
    ∃ K : Set (G E s), IsCompact K ∧
      ∀ (c : Matrix n₀ p (𝔸 E)) (b : Matrix p p (𝔸 E)),
        ∃ (y : Matrix n₀ p (𝔸 E)) (z : Matrix p p (𝔸 E)),
          D.radicalElement y z ∈ V.Γ ∧ D.radicalElement y z * D.radicalElement c b ∈ K := by
  -- Move first `c`, then `b`, into a compact set by rational matrices; `D.radicalElement y z` lies
  -- in `V.Γ` when `V₀.x * y` and `z` are rational.
  obtain ⟨C, hC, h_coverC⟩ : ∃ C : Set (Matrix n₀ p (𝔸 E)), IsCompact C ∧
      ∀ x : Matrix n₀ p (𝔸 E), ∃ γ ∈ ratMatrices E n₀ p, γ + x ∈ C :=
    IsCovolOneLattice.exists_compact_cover (ratMatrices E n₀ p)
  obtain ⟨B, hB, h_coverB⟩ : ∃ B : Set (Matrix p p (𝔸 E)), IsCompact B ∧
      ∀ x : Matrix p p (𝔸 E), ∃ γ ∈ ratMatrices E p p, γ + x ∈ B :=
    IsCovolOneLattice.exists_compact_cover (ratMatrices E p p)
  let φ (x : Matrix n₀ p (𝔸 E) × Matrix p p (𝔸 E)) : G E s :=
    D.radicalElement (V₀.x⁻¹.val * x.fst) x.snd
  refine ⟨φ '' C ×ˢ B, (hC.prod hB).image (by fun_prop), fun c b ↦ ?_⟩
  obtain ⟨γ, ⟨y₀, hy₀⟩, h_memC⟩ : ∃ γ ∈ ratMatrices E n₀ p, γ + V₀.x.val * c ∈ C := h_coverC _
  obtain rfl : y₀.map toAdele = γ := hy₀
  let y : Matrix n₀ p (𝔸 E) := V₀.x⁻¹.val * y₀.map toAdele
  obtain ⟨z, hz, h_memB⟩ : ∃ z ∈ ratMatrices E p p,
      z + (toAdele (j : E) • yᴴ * stdForm E s₀ * c + b) ∈ B := h_coverB _
  refine ⟨y, z, D.radicalElement_mem_Gamma y₀ hz, (_, _), ⟨h_memC, h_memB⟩, ?_⟩
  -- The parameters of the product are those that were moved into `C` and `B`.
  have h_first : V₀.x⁻¹.val * (y₀.map toAdele + V₀.x.val * c) = y + c := by
    simp [y, Matrix.mul_add]
  simp only [φ, h_first, radicalElement_mul, add_assoc]

omit [WeilData E] in
/-- The adelic frame `k` sends vectors with entries in `E` to rational vectors of `V`. -/
lemma kAdelic_mulVec_mem_ratVectors {b : p → 𝔸 E} :
    b ∈ New.ratVectors E p → D.kAdelic *ᵥ b ∈ V.ratVectors := by
  rintro ⟨a, rfl⟩
  refine ⟨D.k *ᵥ a, ?_⟩
  aesop (add simp [kAdelic, vecAtPoint, comp_def, RingHom.map_mulVec])

end Space.Splitting

end New

end Splitting

/-! ## Two opposite parabolic subgroups generate the group of a split space -/

section SiegelParabolic

namespace New

open Matrix Polynomial

variable {E p : Type*} [Field E] [CMType E] [Fintype p]

/-- The standard hermitian form `xᴴ x` over the CM field `E` is anisotropic. -/
lemma eq_zero_of_star_dotProduct_self {x : p → E} (hx : star x ⬝ᵥ x = 0) : x = 0 := by
  -- Any complex embedding `φ` turns the conjugation of `E` into complex conjugation.
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h_image : star (φ ∘ x) ⬝ᵥ (φ ∘ x) = 0 := by
    simpa [dotProduct, map_star_complex] using congrArg φ hx
  open ComplexOrder in
  exact φ.injective.comp_left (by simpa using dotProduct_star_self_eq_zero.1 h_image)

/-- Let `a`, `c` be square matrices over the CM field `E` with `aᴴ c + cᴴ a = 0` and with no common
kernel. Then `a + t c` is invertible for some purely imaginary scalar `t`. -/
lemma exists_skew_isUnit_add_smul [WeilData E] [DecidableEq p] {a c : Matrix p p E}
    (h_iso : aᴴ * c + cᴴ * a = 0) (h_ker : ∀ v : p → E, a *ᵥ v = 0 → c *ᵥ v = 0 → v = 0) :
    ∃ t : E, star t = -t ∧ IsUnit (a + t • c) := by
  -- The polynomial `det (a + X c)` does not vanish at `1`, so it has finitely many roots.
  -- Indeed `(a + c)ᴴ (a + c) = aᴴ a + cᴴ c` is definite: `(a + c) v = 0` gives `a v = c v = 0`.
  have h_gram : (a + c)ᴴ * (a + c) = aᴴ * a + cᴴ * c :=
    calc (a + c)ᴴ * (a + c)
      _ = aᴴ * a + cᴴ * c + (aᴴ * c + cᴴ * a) := by
        rw [conjTranspose_add]
        noncomm_ring
      _ = aᴴ * a + cᴴ * c := by rw [h_iso, add_zero]
  have h_one : (a + c).det ≠ 0 := by
    rw [Ne, ← exists_mulVec_eq_zero_iff]
    rintro ⟨v, hv_ne, hv⟩
    have h_form (m : Matrix p p E) : star (m *ᵥ v) ⬝ᵥ m *ᵥ v = star v ⬝ᵥ (mᴴ * m) *ᵥ v := by
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
    let u : p ⊕ p → E := Sum.elim (a *ᵥ v) (c *ᵥ v)
    have h_zero : u = 0 := eq_zero_of_star_dotProduct_self <|
      calc star u ⬝ᵥ u
        _ = star (a *ᵥ v) ⬝ᵥ a *ᵥ v + star (c *ᵥ v) ⬝ᵥ c *ᵥ v := by simp [u, dotProduct]
        _ = star ((a + c) *ᵥ v) ⬝ᵥ (a + c) *ᵥ v := by
          simp only [h_form, h_gram, add_mulVec (aᴴ * a), dotProduct_add]
        _ = 0 := by rw [hv, dotProduct_zero]
    exact hv_ne (h_ker v (congrArg (· ∘ Sum.inl) h_zero) (congrArg (· ∘ Sum.inr) h_zero))
  let P : E[X] := (a.map C + (X : E[X]) • c.map C).det
  have h_eval (t : E) : P.eval t = (a + t • c).det := by
    rw [← coe_evalRingHom, RingHom.map_det]
    exact congrArg det (Matrix.ext fun i j ↦ by simp [mul_comm t])
  have h_ne : P ≠ 0 := fun h_zero ↦ h_one (by simpa [h_zero] using (h_eval 1).symm)
  -- The multiples of `j` by natural numbers are infinitely many purely imaginary scalars.
  have h_inf : (Set.range fun m : ℕ ↦ (m : E) * WeilData.j).Infinite :=
    Set.infinite_range_of_injective
      ((mul_left_injective₀ WeilData.j_ne_zero).comp Nat.cast_injective)
  obtain ⟨t, ⟨m, rfl⟩, h_root⟩ : ∃ t ∈ Set.range fun m : ℕ ↦ (m : E) * WeilData.j, ¬P.IsRoot t :=
    h_inf.exists_notMem_finite (finite_setOfPred_isRoot h_ne)
  have h_det : (a + ((m : E) * WeilData.j) • c).det ≠ 0 := by rwa [← h_eval]
  exact ⟨m * WeilData.j, by simp [WeilData.star_j], (isUnit_iff_isUnit_det _).2 h_det.isUnit⟩

namespace Space.Splitting

variable [DecidableEq p] {n : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  {V : Space E n s} (D : V.Splitting (stdSpace E Empty) p)

/-- The parabolic subgroup of a splitting `D` without middle part: the rational unitary `γ` that
map the maximal isotropic subspace spanned by the frame `D.k` onto itself. The opposite parabolic
subgroup, of the dual frame `D.l`, is `D.symm.siegelParabolic`. -/
def siegelParabolic : Subgroup (U V.J) where
  carrier := {γ : U V.J | ∃ a : GL p E, γ.val.val * D.k = D.k * a.val}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro γ δ ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by simp [Matrix.mul_assoc, hb, ← Matrix.mul_assoc γ.val.val, ha]⟩
  inv_mem' := by
    rintro γ ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    calc γ⁻¹.val.val * D.k
      _ = γ⁻¹.val.val * (γ.val.val * D.k) * a⁻¹.val := by simp [ha, Matrix.mul_assoc]
      _ = D.k * a⁻¹.val := by simp

/-- For a skew-hermitian matrix `b`, the translation `k ↦ k`, `l ↦ l + k b` of the frames of `D` is
given by an element of the parabolic subgroup of `D`. -/
lemma exists_mem_siegelParabolic_mul_l_eq {b : Matrix p p E} (hb : bᴴ = -b) :
    ∃ u ∈ D.siegelParabolic, u.val.val * D.k = D.k ∧ u.val.val * D.l = D.l + D.k * b := by
  have h_kk (X : Matrix p n E) : D.kᴴ * (V.J * (D.k * X)) = 0 := by simp [← Matrix.mul_assoc]
  have h_form : (1 + D.k * b * (D.kᴴ * V.J))ᴴ * V.J * (1 + D.k * b * (D.kᴴ * V.J)) = V.J := by
    simp [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, V.conjTranspose_J, hb, h_kk]
  let u : U V.J := U.of V.isUnit_J _ h_form
  have hu (X : Matrix n p E) : u.val.val * X = X + D.k * b * (D.kᴴ * V.J * X) := by
    simp [u, Matrix.add_mul, Matrix.mul_assoc]
  have h_k : u.val.val * D.k = D.k := by rw [hu, D.gram_kk, Matrix.mul_zero, add_zero]
  exact ⟨u, ⟨1, by simpa using h_k⟩, h_k, by rw [hu, D.gram_kl, Matrix.mul_one]⟩

variable {D} {g : U V.J} {a c : Matrix p p E}

/-- If `g k = k a + l c` for a unitary `g`, then `aᴴ c + cᴴ a = 0`, as `g k` is isotropic. -/
lemma conjTranspose_mul_add_eq_zero (hg : g.val.val * D.k = D.k * a + D.l * c) :
    aᴴ * c + cᴴ * a = 0 := by
  have h_gram (X Y : Matrix n p E) (x y : Matrix p p E) :
      (X * x)ᴴ * V.J * (Y * y) = xᴴ * (Xᴴ * V.J * Y) * y := by simp [Matrix.mul_assoc]
  calc aᴴ * c + cᴴ * a
    _ = (D.k * a + D.l * c)ᴴ * V.J * (D.k * a + D.l * c) := by
      simp [Matrix.add_mul, Matrix.mul_add, h_gram, add_comm, -conjTranspose_mul]
    _ = 0 := by rw [← hg, U.gram_invariant, D.gram_kk]

/-- The big cell: if `g k = k a + l c` with `a` invertible, then some element of the opposite
parabolic subgroup moves `g` into the parabolic subgroup of `D`. -/
lemma exists_mul_mem_siegelParabolic (hg : g.val.val * D.k = D.k * a + D.l * c) (ha : IsUnit a) :
    ∃ v ∈ D.symm.siegelParabolic, v * g ∈ D.siegelParabolic := by
  -- Take the translation `l ↦ l`, `k ↦ k - l c a⁻¹`.
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨v, hv, hv_l, hv_k⟩ := D.symm.exists_mem_siegelParabolic_mul_l_eq (b := -(c * a⁻¹.val)) (by
    rw [show (-(c * a⁻¹.val))ᴴ = -(a⁻¹.valᴴ * (cᴴ * a) * a⁻¹.val) by simp [Matrix.mul_assoc]]
    simp [eq_neg_of_add_eq_zero_right (conjTranspose_mul_add_eq_zero hg),
      ← Matrix.mul_assoc, ← conjTranspose_mul])
  refine ⟨v, hv, a, ?_⟩
  rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, hg, Matrix.mul_add, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, show v.val.val * D.k = _ from hv_k, show v.val.val * D.l = _ from hv_l]
  simp [symm, Matrix.add_mul, Matrix.mul_assoc]

variable (D)

/-- In a splitting without middle part every vector is the sum of its components along the frames
`k` and `l`. -/
lemma k_mul_add_l_mul_eq_one : D.k * (D.lᴴ * V.J) + D.l * (D.kᴴ * V.J) = 1 := by
  have h_card : Fintype.card n = Fintype.card (p ⊕ p) := by simp [D.card_eq, two_mul]
  rw [← fromCols_mul_fromRows, mul_eq_one_comm_of_card_eq _ _ _ h_card, fromRows_mul_fromCols,
    D.gram_lk, D.gram_ll, D.gram_kk, D.gram_kl, fromBlocks_one]

/-- Let `D` be a splitting of `V` without middle part. The stabilizers of the spans of the two
isotropic frames `D.k` and `D.l` generate the rational unitary group of `V`. -/
lemma siegelParabolic_sup_symm_eq_top [WeilData E] :
    D.siegelParabolic ⊔ D.symm.siegelParabolic = ⊤ := by
  -- Write `g k = k a + l c`. A translation `u : l ↦ l + t k` turns `a` into `a + t c`, which is
  -- invertible for a suitable `t`; then `u g` lies in the big cell.
  refine eq_top_iff.2 fun g _ ↦ ?_
  obtain ⟨a, c, hg⟩ : ∃ a c : Matrix p p E, g.val.val * D.k = D.k * a + D.l * c := by
    refine ⟨D.lᴴ * V.J * (g.val.val * D.k), D.kᴴ * V.J * (g.val.val * D.k), ?_⟩
    rw [← Matrix.mul_assoc D.k, ← Matrix.mul_assoc D.l, ← Matrix.add_mul, k_mul_add_l_mul_eq_one,
      Matrix.one_mul]
  have h_ker (v : p → E) (hav : a *ᵥ v = 0) (hcv : c *ᵥ v = 0) : v = 0 :=
    calc v
      _ = ((g.val.val * D.l)ᴴ * V.J) *ᵥ (g.val.val * D.k) *ᵥ v := by
        rw [mulVec_mulVec, U.gram_invariant, D.gram_lk, one_mulVec]
      _ = 0 := by simp [hg, add_mulVec, ← mulVec_mulVec, hav, hcv]
  obtain ⟨t, ht, h_unit⟩ : ∃ t : E, star t = -t ∧ IsUnit (a + t • c) :=
    exists_skew_isUnit_add_smul (conjTranspose_mul_add_eq_zero hg) h_ker
  obtain ⟨u, hu, hu_k, hu_l⟩ : ∃ u ∈ D.siegelParabolic,
      u.val.val * D.k = D.k ∧ u.val.val * D.l = D.l + D.k * (t • 1) :=
    D.exists_mem_siegelParabolic_mul_l_eq (by simp [ht])
  have h_ug : (u * g).val.val * D.k = D.k * (a + t • c) + D.l * c := by
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, hg, Matrix.mul_add,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hu_k, hu_l]
    simp [Matrix.add_mul, Matrix.mul_add, add_assoc, add_comm (D.l * c)]
  obtain ⟨v, hv, h_vug⟩ : ∃ v ∈ D.symm.siegelParabolic, v * (u * g) ∈ D.siegelParabolic :=
    exists_mul_mem_siegelParabolic h_ug h_unit
  rw [← mul_mem_cancel_left (Subgroup.mem_sup_left hu),
    ← mul_mem_cancel_left (Subgroup.mem_sup_right hv)]
  exact Subgroup.mem_sup_left h_vug

end Space.Splitting

end New

end SiegelParabolic

end
