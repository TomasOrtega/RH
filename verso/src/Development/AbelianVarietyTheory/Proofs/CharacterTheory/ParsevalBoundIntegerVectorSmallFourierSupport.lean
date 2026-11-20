import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : ‖ω‖ = 1` using `hω.norm'_eq_one hN.ne'`. Establish `h0 : ω ≠ 0` using `hω.ne_zero hN.ne'`. Rewrite using `[← Complex.inv_eq_conj h1]`. Establish `hz : ∀ j : ℕ, ω ^ (j * k) * (ω⁻¹) ^ (j * l) = (ω ^ k * (ω ^ l)⁻¹) ^ j`. Introduce `j`.

Rewrite using `[mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm l]`. Repeatedly rewrite using `[hz]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `[mul_inv_cancel₀ (pow_ne_zero k h0)]`.

Establish `hne : ω ^ k * (ω ^ l)⁻¹ ≠ 1`. Introduce `h'`. Apply `h` to reduce the goal to its premises. Apply `hω.pow_inj hk hl` to reduce the goal to its premises. Clear denominators, using `at h'` for the nonvanishing conditions.

Conclude with `h'`. Establish `hp : (ω ^ k * (ω ^ l)⁻¹) ^ N = 1`. Rewrite using `[mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm l, pow_mul, pow_mul, hω.pow_eq_one]`. Simplify using the standard rewrite rules. Rewrite using `[geom_sum_eq hne, hp]`.

Simplify using the standard rewrite rules.
-/
theorem parsevalSep_orth (N : ℕ) (ω : ℂ) (hN : 0 < N) (hω : IsPrimitiveRoot ω N) (k l : ℕ)
    (hk : k < N) (hl : l < N) :
    ∑ j ∈ Finset.range N, ω ^ (j * k) * (starRingEnd ℂ ω) ^ (j * l)
      = if k = l then (N : ℂ) else 0 := by
  have h1 : ‖ω‖ = 1 := hω.norm'_eq_one hN.ne'
  have h0 : ω ≠ 0 := hω.ne_zero hN.ne'
  rw [← Complex.inv_eq_conj h1]
  have hz : ∀ j : ℕ, ω ^ (j * k) * (ω⁻¹) ^ (j * l) = (ω ^ k * (ω ^ l)⁻¹) ^ j := by
    intro j
    rw [mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm l]
  simp_rw [hz]
  split_ifs with h
  · subst h
    simp [mul_inv_cancel₀ (pow_ne_zero k h0)]
  · have hne : ω ^ k * (ω ^ l)⁻¹ ≠ 1 := by
      intro h'
      apply h
      apply hω.pow_inj hk hl
      field_simp at h'
      exact h'
    have hp : (ω ^ k * (ω ^ l)⁻¹) ^ N = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm l, pow_mul, pow_mul,
        hω.pow_eq_one]
      simp
    rw [geom_sum_eq hne, hp]
    simp

/- English proof (translation)
Apply `Complex.ofReal_injective` to reduce the goal to its premises. Use `push_cast`. Repeatedly rewrite using `[← Complex.mul_conj', map_sum, Finset.sum_mul_sum, map_mul, map_pow, map_intCast]`. Rewrite using `[Finset.sum_comm, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Establish `: ∀ l ∈ Finset.range N, ∑ j ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k) * ((c l : ℂ) * (starRingEnd ℂ ω) ^ (j * l)) = if k = l then (c k : ℂ) * c l * N else 0`. Introduce `l hl`. Use `parsevalSep_orth N ω hN hω k l (Finset.mem_range.1 hk) (Finset.mem_range.1 hl)` as an intermediate fact. Establish `e : ∑ j ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k) * ((c l : ℂ) * (starRingEnd ℂ ω) ^ (j * l)) = (c k : ℂ) * c l * ∑ j ∈ Finset.range N, ω ^ (j * k) * (starRingEnd ℂ ω) ^ (j * l)`.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[e, this]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos hk]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem parsevalSep_identity (N : ℕ) (ω : ℂ) (hN : 0 < N) (hω : IsPrimitiveRoot ω N)
    (c : ℕ → ℤ) :
    ∑ j ∈ Finset.range N, ‖∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k)‖ ^ 2
      = (N : ℝ) * ((∑ k ∈ Finset.range N, c k ^ 2 : ℤ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, map_mul, map_pow, map_intCast]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_comm]
  have : ∀ l ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (c k : ℂ) * ω ^ (j * k) * ((c l : ℂ) * (starRingEnd ℂ ω) ^ (j * l))
      = if k = l then (c k : ℂ) * c l * N else 0 := by
    intro l hl
    have := parsevalSep_orth N ω hN hω k l (Finset.mem_range.1 hk) (Finset.mem_range.1 hl)
    have e : ∑ j ∈ Finset.range N,
      (c k : ℂ) * ω ^ (j * k) * ((c l : ℂ) * (starRingEnd ℂ ω) ^ (j * l))
       = (c k : ℂ) * c l * ∑ j ∈ Finset.range N, ω ^ (j * k) * (starRingEnd ℂ ω) ^ (j * l) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, this]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos hk]
  ring

/- English proof (translation)
Introduce `n N ω c S hn hN hω h2 h0 hS`. Establish `h1 : ‖ω‖ = 1` using `hω.norm'_eq_one hN.ne'`. Establish `hP` using `parsevalSep_identity N ω hN hω c`. Rewrite `hP` using `[h2]`. Use `set F : ℕ → ℂ := fun j => ∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k) with hF`.

Establish `hb : ∀ j, ‖F j‖ ≤ 2 * n`. Introduce `j`. Establish `h2' : ∑ k ∈ Finset.range N, (c k : ℝ) ^ 2 = 2 * n` using `by exact_mod_cast h2`. Rewrite using `[← h2']`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_pow, h1, one_pow, mul_one, Complex.norm_intCast]`. Establish `: |c k| ≤ c k ^ 2`. Rewrite using `[← sq_abs]`. Use `abs_nonneg (c k)` as an intermediate fact. Use polynomial arithmetic with `[Int.le_self_sq |c k|]`.

Conclude with `this` after adjusting the coercions. Establish `hz : ‖F 0‖ ≤ (n : ℝ) - 1`. Establish `: F 0 = ((∑ k ∈ Finset.range N, c k : ℤ) : ℂ)` using `by simp [hF]`. Rewrite using `[this, Complex.norm_intCast]`. Conclude with `h0` after adjusting the coercions.

Establish `hle : ∀ j ∈ Finset.range N, ‖F j‖ ^ 2 ≤ (if j = 0 then ((n : ℝ) - 1) ^ 2 else 0) + (if j ∈ S then 4 * (n : ℝ) ^ 2 else 0)`. Introduce `j hj`. Distinguish the cases in `hj0 : j = 0`. Substitute `hj0` using the available equality. Establish `: ‖F 0‖ ^ 2 ≤ ((n : ℝ) - 1) ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) hz 2`.

Rewrite using `[if_pos rfl]`. Use `split_ifs`. Establish `: (0 : ℝ) ≤ 4 * (n : ℝ) ^ 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[if_neg hj0, zero_add] split_ifs with hjS`. Use `pow_le_pow_left₀ (norm_nonneg _) (hb j) 2` as an intermediate fact. Combine the linear relations using `[show (2 * (n : ℝ)) ^ 2 = 4 * (n : ℝ) ^ 2 by ring]`. Establish `: F j = 0` using `hS j (Nat.pos_of_ne_zero hj0) (Finset.mem_range.1 hj) hjS`. Simplify using `[this]`.

Establish `hsum` using `Finset.sum_le_sum hle`. Rewrite `hsum` using `[Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_range.2 hN), Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]`. Establish `hc : ((Finset.range N ∩ S).card : ℝ) ≤ S.card`. Conclude with `Finset.card_le_card Finset.inter_subset_right` after adjusting the coercions. Establish `hP' : ∑ j ∈ Finset.range N, ‖F j‖ ^ 2 = (N : ℝ) * (2 * n)`.

Rewrite using `[hP]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `key : (2 * n * N : ℝ) ≤ ((n : ℝ) - 1) ^ 2 + 4 * (n : ℝ) ^ 2 * S.card`. Establish `: ((Finset.range N ∩ S).card : ℝ) * (4 * (n : ℝ) ^ 2) ≤ S.card * (4 * (n : ℝ) ^ 2)` using `mul_le_mul_of_nonneg_right hc (by positivity)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1`. Rewrite using `[Nat.cast_sub hn]`. Simplify using the standard rewrite rules. Rewrite `key` using `[← hn1]`.

Conclude with `key` after adjusting the coercions.
-/
theorem parsevalSep_bound : ∀ (n N : ℕ) (ω : ℂ) (c : ℕ → ℤ) (S : Finset ℕ), 0 < n → 0 < N → IsPrimitiveRoot ω N → ∑ k ∈ Finset.range N, c k ^ 2 = 2 * n → |∑ k ∈ Finset.range N, c k| ≤ (n : ℤ) - 1 → (∀ j : ℕ, 0 < j → j < N → j ∉ S → ∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k) = 0) → 2 * n * N ≤ (n - 1) ^ 2 + 4 * n ^ 2 * S.card := by
  intro n N ω c S hn hN hω h2 h0 hS
  have h1 : ‖ω‖ = 1 := hω.norm'_eq_one hN.ne'
  have hP := parsevalSep_identity N ω hN hω c
  rw [h2] at hP
  set F : ℕ → ℂ := fun j => ∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k) with hF
  have hb : ∀ j, ‖F j‖ ≤ 2 * n := by
    intro j
    have h2' : ∑ k ∈ Finset.range N, (c k : ℝ) ^ 2 = 2 * n := by exact_mod_cast h2
    rw [← h2']
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_pow, h1, one_pow, mul_one, Complex.norm_intCast]
    have : |c k| ≤ c k ^ 2 := by
      rw [← sq_abs]
      have := abs_nonneg (c k)
      nlinarith [Int.le_self_sq |c k|]
    exact_mod_cast this
  have hz : ‖F 0‖ ≤ (n : ℝ) - 1 := by
    have : F 0 = ((∑ k ∈ Finset.range N, c k : ℤ) : ℂ) := by simp [hF]
    rw [this, Complex.norm_intCast]
    exact_mod_cast h0
  have hle : ∀ j ∈ Finset.range N, ‖F j‖ ^ 2 ≤
      (if j = 0 then ((n : ℝ) - 1) ^ 2 else 0) + (if j ∈ S then 4 * (n : ℝ) ^ 2 else 0) := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      have : ‖F 0‖ ^ 2 ≤ ((n : ℝ) - 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      rw [if_pos rfl]
      split_ifs
      · have : (0 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by positivity
        linarith
      · linarith
    · rw [if_neg hj0, zero_add]
      split_ifs with hjS
      · have := pow_le_pow_left₀ (norm_nonneg _) (hb j) 2
        linarith [show (2 * (n : ℝ)) ^ 2 = 4 * (n : ℝ) ^ 2 by ring]
      · have : F j = 0 := hS j (Nat.pos_of_ne_zero hj0) (Finset.mem_range.1 hj) hjS
        simp [this]
  have hsum := Finset.sum_le_sum hle
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_range.2 hN),
    Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : ((Finset.range N ∩ S).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hP' : ∑ j ∈ Finset.range N, ‖F j‖ ^ 2 = (N : ℝ) * (2 * n) := by
    rw [hP]; push_cast; ring
  have key : (2 * n * N : ℝ) ≤ ((n : ℝ) - 1) ^ 2 + 4 * (n : ℝ) ^ 2 * S.card := by
    have : ((Finset.range N ∩ S).card : ℝ) * (4 * (n : ℝ) ^ 2) ≤ S.card * (4 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    linarith
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; simp
  rw [← hn1] at key
  exact_mod_cast key

end GlobalTheory
