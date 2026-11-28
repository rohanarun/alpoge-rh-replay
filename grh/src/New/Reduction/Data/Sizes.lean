module

public import New.Reduction.Data.LevelAndTwists

/-!
# Sizes of the data

This file proves size estimates for admissible data `D : Data P`: for the scales, the ranks, the
field and the primes. The table recalls the main sizes, including those proved in the imported
files. Each quantity has bounds `exp l ≤ F` and `|F| ≤ exp l'` that instance search finds and
carries through sums, products and powers; `le_of_hasLogBound` proves `F ≤ G` by comparing the upper
exponent of `F` with the lower exponent of `G`, using the inequalities between the scales.

| quantity | size proved | degree in `x` |
|---|---|---|
| `s`, `l₀` | `s ≤ 32 log x`, `27 s < l₀ ≤ 81 s` | `0` |
| `log x₁`, `log b` | `(log x₁)⁶ ≤ log b`, `(log b)¹⁰⁰ ≤ x` | `≤ 1 / 100` |
| `m` | `[√x, 2 √x]` | `1 / 2` |
| `k`, `r`, `t` | `r` in `[x⁵, 3 x⁵]`, `k ≤ r ≤ 2 k`, `t = 5 r` | `5` |
| `n_m` | `k + m (t + 1)` | `11 / 2` |
| `2 ^ s`, `f`, `q₁` | `x¹¹ ≤ m ^ 22 = 2 ^ s ≤ f ≤ q₁ ≤ x¹²` | `11`; the upper bound is rounded up |
| `rootDisc`, `1 / Ω` | `[x¹⁰, x¹²]`, `[1, x¹³]` | `11`; the bounds are rounded |
| the gap `Δ = D.gap` | `2 r⁸` | `40` |
| `x₁` | `x ^ 10⁶ ≤ x₁` | at least `10⁶` |
| `b`, `a = x b`, the weights `κ` | `x₁ ^ 10⁶ ≤ b`, `a / x₁ ≤ κ ≤ b` | |
| `M = p₀ p₁` | `[b²⁰, b²²]` | |
| `N` | `log N` in `[m log b, 30 m log b]` | |

Notions from other files:
* `Data P`: admissible data over the parameters `P`; among its fields are the logarithms `logX`,
  `logX₁`, `logB` of the scales `x`, `x₁`, `b`, the numbers `m`, `r`, `towerExp` (the `s` of the
  table), the primes `levelPrime 0`, `levelPrime 1` and the level `N`.
* `D.E`: the CM field `K(ζ_{q₁})` over `K = ℚ(√-d)`, with `D.f` infinite places and root
  discriminant `rd_E = D.rootDisc`.
* `P.bigOmega s`: the real number `Ω = exp (γ - Re L'/L(1, χ_K)) · 2π / rd_E`.
-/

@[expose] public section

namespace New.Data

open Real Set Parameters

variable {P : Parameters} (D : Data P)

/-! ### Scales and the exponent of the tower -/

/-- The exponent `s = D.towerExp` of the tower of admissible data `D`, for which `2 ^ s = m ^ 22`
with `m = D.m ≥ 2`, is not zero. -/
lemma towerExp_ne_zero : D.towerExp ≠ 0 := by
  obtain ⟨e, -, hs⟩ : ∃ e : ℕ, D.m = 2 ^ (e + 1) ∧ D.towerExp = (e + 1) * 22 :=
    D.exists_m_eq_two_pow
  omega

/-- The scales `x₁` and `b` of admissible data satisfy `x₁ ^ (3 l₀²) ≤ √b`, where `l₀` is the least
power of `3` above `27 s` and `s` is the exponent of the tower. -/
lemma x₁_pow_le_sqrt_b : D.x₁ ^ (3 * l₀ D.towerExp ^ 2) ≤ √D.b := by
  have hl₀_le : (l₀ D.towerExp : ℝ) ≤ 81 * D.towerExp := mod_cast l₀_le_mul D.towerExp_ne_zero
  have h_logX₁_pos : 0 < D.logX₁ := HasLogBound.pos D
  rw [x₁, b, ← exp_natCast_mul, ← exp_half, exp_le_exp]
  push_cast
  -- By sizes: `s ≤ 32 log x`, `log x ≤ log x₁`, `(log x₁) ^ 6 ≤ log b`, and `log x₁` is large.
  calc 3 * (l₀ D.towerExp : ℝ) ^ 2 * D.logX₁ ≤ 3 * (81 * D.towerExp) ^ 2 * D.logX₁ := by gcongr
    _ ≤ D.logB / 2 := D.le_of_hasLogBound

/-! ### Ranks and invariants of the field

The numbers `m`, `k` are even and `r`, `t` are odd by the imported lemmas `m_even`, `k_even`,
`r_odd`, `t_odd`; hence every `n_j = k + j (t + 1)` is even (`New.Data.n_even`). -/

/-- The rank `m = D.m` and the exponent `s = D.towerExp` of the field `E = P.E s` of the data `D`
satisfy `m ^ 22 = 2 ^ s`. -/
lemma m_pow_eq_two_pow_towerExp : D.m ^ 22 = 2 ^ D.towerExp := by
  obtain ⟨e, hm, hs⟩ : ∃ e : ℕ, D.m = 2 ^ (e + 1) ∧ D.towerExp = (e + 1) * 22 :=
    D.exists_m_eq_two_pow
  rw [hm, hs, pow_mul]

/-- The number `m` of successive theta lifts of admissible data, a power of `2`, satisfies
`m ^ 594 ≤ 2 ^ l₀`. Here `s = D.towerExp` is the exponent with `m ^ 22 = 2 ^ s`, and `l₀ = l₀ s` is
the least power of `3` above `27 s`. -/
lemma m_pow_le_two_pow_l₀ : D.m ^ 594 ≤ 2 ^ l₀ D.towerExp :=
  calc D.m ^ 594 = (D.m ^ 22) ^ 27 := by rw [← pow_mul]
    _ = 2 ^ (27 * D.towerExp) := by rw [m_pow_eq_two_pow_towerExp, ← pow_mul, mul_comm]
    _ ≤ 2 ^ l₀ D.towerExp := Nat.pow_le_pow_right two_pos (mul_lt_l₀ D.towerExp).le

/-- The number `f` of infinite places of the field `E = K(ζ_{q₁})`, `K = ℚ(√-d)`, satisfies
`m ^ 22 ≤ f ≤ q₁`. Here `m` is the number of successive theta lifts, a power of `2` with
`m ^ 22 = 2 ^ s` for `s = D.towerExp`, and `q₁ = 3 l₀ 2 ^ s q₀` is the order of the root of unity,
with `l₀` the least power of `3` above `27 s` and `q₀` the fixed modulus of the parameters. -/
lemma f_mem_Icc : D.f ∈ Icc (D.m ^ 22) D.q₁ := by
  rw [show D.f = towerDeg D.towerExp * P.q₀.totient from P.numInfPlaces_E D.towerExp]
  constructor
  · calc D.m ^ 22 = 2 ^ D.towerExp := D.m_pow_eq_two_pow_towerExp
      _ ≤ towerDeg D.towerExp := Nat.le_mul_of_pos_left _ (by positivity)
      _ ≤ towerDeg D.towerExp * P.q₀.totient := Nat.le_mul_of_pos_right _ (NeZero.pos _)
  · rw [q₁, Parameters.q₁, mul_comm P.q₀]
    exact Nat.mul_le_mul_left _ (Nat.totient_le _)

/-- The number `f` of infinite places of the field `E` of the data is even. -/
lemma f_even : Even D.f := by
  rw [f, P.numInfPlaces_E, towerDeg]
  simp [Nat.even_pow, D.towerExp_ne_zero]

/-- The modulus `q₂ s = (q₀ d) ^ (s + 6)` is at most `x ^ (33 q₀ d)`. Here `q₀`, a multiple of
`18480`, and the prime `d` with `K = ℚ(√-d)` are the fixed parameters, `s` is the exponent of the
tower and `x = exp logX` is the length of the prime sum. -/
lemma q₂_le : (P.q₂ D.towerExp : ℝ) ≤ D.x ^ (33 * (P.q₀ * P.d)) := by
  have h_exponent : (D.towerExp + 6 : ℝ) ≤ 33 * D.logX := by
    linarith [D.towerExp_le, D.constantBound_le, D.mul_log_logB_le_logX,
      (le_constantBound (P := P)).1]
  calc (P.q₂ D.towerExp : ℝ) = ((P.q₀ * P.d : ℕ) : ℝ) ^ (D.towerExp + 6) := by rw [q₂, Nat.cast_pow]
    _ ≤ exp (P.q₀ * P.d : ℕ) ^ (D.towerExp + 6) := by
      gcongr
      linarith only [add_one_le_exp ((P.q₀ * P.d : ℕ) : ℝ)]
    _ = exp ((D.towerExp + 6) * (P.q₀ * P.d : ℕ)) := by
      rw [← exp_natCast_mul, Nat.cast_add, Nat.cast_ofNat]
    _ ≤ exp (33 * D.logX * (P.q₀ * P.d : ℕ)) := by gcongr
    _ = D.x ^ (33 * (P.q₀ * P.d)) := by simp [← exp_natCast_mul, mul_right_comm]

/-- The class number `h_E` of the CM field `E` of admissible data satisfies `log h_E ≤ x ^ 30`,
where `x = exp logX` is the length of the prime sum. -/
lemma log_classNumber_le : log (NumberField.classNumber D.E) ≤ D.x ^ 30 := by
  -- `h_E ≤ (2 ^ n |d_E|) ^ (n + 1)` with degree `n = 2 f` and `|d_E| = rd_E ^ (2 f)`.
  have h_discr : ((NumberField.discr D.E).natAbs : ℝ) = (D.rootDisc ^ D.f) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_discr_eq_rootDiscr_pow]
  have h_bound : (NumberField.classNumber D.E : ℝ) ≤
      (2 ^ (2 * D.f) * (D.rootDisc ^ D.f) ^ 2) ^ (2 * D.f + 1) := by
    rw [f, ← finrank_eq_two_mul_card_infinitePlace, ← h_discr]
    exact_mod_cast classNumber_le D.E
  -- The last step compares sizes: `f ≤ x¹²` and `log rd_E ≤ 12 log x`.
  calc _ ≤ log ((2 ^ (2 * D.f) * (D.rootDisc ^ D.f) ^ 2) ^ (2 * D.f + 1)) :=
        log_le_log (mod_cast NumberField.classNumber_pos D.E) h_bound
    _ ≤ D.x ^ 30 := D.le_of_hasLogBound (by scale_grind D)

/-! ### Weights

The bounds `a / x₁ ≤ κ ≤ b` and `κ + x⁴² ≤ 2 b` for the weight `κ = D.weight σ` are the imported
lemmas `weight_mem_Icc`, `weight_le_b` and `weight_add_x_pow_le_two_mul_b`; those for the sequence
`D.shiftedWeight` are `shiftedWeight_mem_Icc` and `log_shiftedWeight_le`. -/

/-! ### Primes, levels and the number `Ω`

The bound `b²⁰ ≤ M ≤ b²²` is `M_mem_Icc`; the range for the level is `logLevelTarget_mem_Icc`,
`log_N_mem_Icc_logLevelTarget` and `log_N_mem_Icc`. How the three primes split in `E` is in
`New.Parameters.star_mem_iff_notMem`, `New.Parameters.intValuation_eq_of_mul_star` and
`New.Data.q_eq_levelPrime`. -/

/-- Each of the two prime factors `p₀ = D.levelPrime 0`, `p₁ = D.levelPrime 1` of the number
`M = p₀ p₁` of admissible data exceeds `b²` and is smaller than the prime `N` (the level). -/
lemma levelPrime_mem_Ioo (i : Fin 2) : (D.levelPrime i : ℝ) ∈ Ioo (D.b ^ 2) D.N :=
  ⟨D.lt_of_hasLogBound, D.lt_of_hasLogBound⟩

/-- For the exponent `s = D.towerExp` of admissible data, the real number
`Ω = P.bigOmega s = exp (γ - Re L'/L(1, χ_K)) · 2π / rd_E` is at most `1`. Here `γ` is Euler's
constant, `χ_K` the quadratic character of `K = ℚ(√-d)` and `rd_E` the root discriminant of the
field `E = P.E s`, a cyclotomic extension of `K`. -/
lemma bigOmega_le_one : P.bigOmega D.towerExp ≤ 1 := by
  -- Instance search knows the upper bound `|Ω| ≤ exp 0`.
  simpa using le_of_abs_le (D.hasLogUpper_iff.1
    (inferInstance : D.HasLogUpper (P.bigOmega D.towerExp) 0))

/-- For admissible data `D` over the parameters `P`, `20 log b ≤ log (M / Ω) ≤ 23 log b`. -/
lemma log_M_div_bigOmega_mem_Icc :
    log (D.M / P.bigOmega D.towerExp) ∈ Icc (20 * D.logB) (23 * D.logB) := by
  have h_lower : D.b ^ 20 ≤ D.M / P.bigOmega D.towerExp :=
    D.M_mem_Icc.1.trans (le_div_self (by positivity) bigOmega_pos D.bigOmega_le_one)
  -- By sizes: `M ≤ b²²` and `1 / Ω ≤ x¹³`.
  have h_upper : D.M / P.bigOmega D.towerExp ≤ D.b ^ 23 := D.le_of_hasLogBound
  constructor
  · simpa using log_le_log (by positivity) h_lower
  · simpa using log_le_log (HasLogBound.pos D) h_upper

/-- For admissible data `D`, `|log (M rd_E / 2π)| ≤ 23 log b`. Here `b = exp D.logB` is the largest
scale, `M = p₀ p₁` is the product of the two distinct primes `pᵢ = D.levelPrime i`, which lie in
`[b¹⁰, b¹¹]`, and `rd_E = D.rootDisc` is the root discriminant of the CM field `E` of the data. -/
lemma abs_log_M_mul_rootDisc_le : |log (D.M * D.rootDisc / (2 * π))| ≤ 23 * D.logB := by
  -- By sizes: `b²⁰ ≤ M ≤ b²²` and `x¹⁰ ≤ rd_E ≤ x¹²`.
  have h_lower : 1 ≤ D.M * D.rootDisc / (2 * π) := D.le_of_hasLogBound
  have h_upper : D.M * D.rootDisc / (2 * π) ≤ D.b ^ 23 := D.le_of_hasLogBound
  rw [abs_of_nonneg (log_nonneg h_lower)]
  simpa using log_le_log (one_pos.trans_le h_lower) h_upper

end New.Data
