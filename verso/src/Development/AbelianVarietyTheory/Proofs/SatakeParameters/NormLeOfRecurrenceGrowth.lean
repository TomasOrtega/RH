import Mathlib

open Finset

namespace GlobalTheory

/- English proof (translation)
Introduce `β a C B m hB ha0 hrec hgrow b hb`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hb0 : b ≠ 0`. Introduce `h`.

Rewrite `hlt` using `[h, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set X : ℂ := b⁻¹ with hX`. Establish `hXn : ‖X‖ = ‖b‖⁻¹` using `norm_inv b`. Establish `hbpos : 0 < ‖b‖` using `norm_pos_iff.mpr hb0`.

Use `set r : ℝ := B * ‖X‖ with hr`. Establish `hrpos : 0 < r` using `by rw [hr, hXn]; positivity`. Establish `hr1 : r < 1`. Rewrite using `[hr, hXn, ← div_eq_mul_inv, div_lt_one hbpos]`. Conclude with `hlt`.

Establish `hes : ∀ k, Multiset.card β < k → β.esymm k = 0`. Introduce `k hk`. Simplify using `[Multiset.esymm, Multiset.powersetCard_eq_empty _ hk]`. Use `set d := Multiset.card β with hd`. Use `set p : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * β.esymm k * X ^ k with hp`.

Establish `hpz : ∀ k ∉ Finset.range (d + 1), p k = 0`. Introduce `k hk`. Simplify using `only [Finset.mem_range, not_lt] at hk`. Simplify using `[hp, hes k (by omega)]`. Establish `hpsum : ∑ k ∈ Finset.range (d + 1), p k = 0`.

Establish `h1` using `congrArg (Polynomial.eval b) (Multiset.prod_X_sub_X_eq_sum_esymm β)`. Rewrite `h1` using `[Polynomial.eval_multiset_prod, Polynomial.eval_finset_sum]`. Establish `hz : (Multiset.map (Polynomial.eval b) (Multiset.map (fun t => Polynomial.X - Polynomial.C t) β)).prod = 0`. Apply `Multiset.prod_eq_zero` to reduce the goal to its premises. Rewrite using `[Multiset.map_map]`.

Conclude with `Multiset.mem_map.mpr ⟨b, hb, by simp⟩`. Rewrite `h1` using `[hz]`. Simplify using `only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X] at h1`. Establish `h2 : ∑ k ∈ Finset.range (d + 1), p k = X ^ d * ∑ j ∈ Finset.range (d + 1), (-1 : ℂ) ^ j * (β.esymm j * b ^ (d - j))`. Rewrite using `[Finset.mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k hk`. Establish `hkd : k ≤ d` using `by rw [Finset.mem_range] at hk; omega`. Establish `hXb : X ^ (d - k) * b ^ (d - k) = 1`. Rewrite using `[← mul_pow, hX, inv_mul_cancel₀ hb0, one_pow]`.

Establish `: X ^ d = X ^ k * X ^ (d - k)` using `by rw [← pow_add, Nat.add_sub_cancel' hkd]`. Simplify using `only [hp]`. Rewrite using `[this]`. Take the linear combination `(-1 : ℂ) ^ k * β.esymm k * X ^ k * hXb.symm`. Rewrite using `[h2, ← h1, mul_zero]`.

Establish `hpsumm : Summable (fun k => ‖p k‖)` using `summable_of_ne_finset_zero (s := Finset.range (d + 1)) (fun k hk => by simp [hpz k hk])`. Establish `hptsum : ∑' k, p k = 0`. Rewrite using `[tsum_eq_sum (s := Finset.range (d + 1)) hpz, hpsum]`. Use `set q : ℕ → ℂ := fun n => a n * X ^ n with hq`. Establish `hgeo : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ m * r ^ n)`.

Establish `h0 : Summable (fun n : ℕ => (n : ℝ) ^ m * r ^ n)` using `summable_pow_mul_geometric_of_norm_lt_one m (by rw [Real.norm_eq_abs, abs_of_pos hrpos]; exact hr1)`. Establish `h1` using `(summable_nat_add_iff 1).mpr h0`. Establish `h2` using `h1.mul_left r⁻¹`. Use `h2.congr (fun n => ?_)` and prove the remaining obligations. Simplify using `only [Nat.cast_add, Nat.cast_one, pow_succ]`.

Clear the denominators using the available nonvanishing facts. Establish `hqsumm : Summable (fun n => ‖q n‖)`. Use `Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hgeo.mul_left C)` and prove the remaining obligations. Simplify using `only [hq, norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hcauchy` using `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hpsumm hqsumm`. Rewrite `hcauchy` using `[hptsum, zero_mul]`. Establish `hterm : ∀ n, ∑ k ∈ Finset.range (n + 1), p k * q (n - k) = X ^ n * ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k)`. Introduce `n`. Rewrite using `[Finset.mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k hk`. Establish `hkn : k ≤ n` using `by rw [Finset.mem_range] at hk; omega`. Establish `: X ^ n = X ^ k * X ^ (n - k)` using `by rw [← pow_add, Nat.add_sub_cancel' hkn]`. Simplify using `only [hp, hq]`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hone : ∑' n, ∑ k ∈ Finset.range (n + 1), p k * q (n - k) = 1`. Rewrite using `[tsum_eq_single 0]`. Simplify using `[hp, hq, ha0, Multiset.esymm, Multiset.powersetCard_zero_left]`.

Introduce `n hn`. Rewrite using `[hterm n, hrec n (Nat.one_le_iff_ne_zero.mpr hn), mul_zero]`. Rewrite `hcauchy` using `[hone]`. Conclude with `zero_ne_one hcauchy`.
-/
theorem norm_le_of_recurrence_growth : ∀ (β : Multiset ℂ) (a : ℕ → ℂ) (C B : ℝ) (m : ℕ), 0 < B → a 0 = 1 → (∀ n, 1 ≤ n → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) = 0) → (∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ m * B ^ n) → ∀ b ∈ β, ‖b‖ ≤ B := by
  intro β a C B m hB ha0 hrec hgrow b hb
  by_contra hlt
  push_neg at hlt
  have hb0 : b ≠ 0 := by
    intro h; rw [h, norm_zero] at hlt; linarith
  set X : ℂ := b⁻¹ with hX
  have hXn : ‖X‖ = ‖b‖⁻¹ := norm_inv b
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  set r : ℝ := B * ‖X‖ with hr
  have hrpos : 0 < r := by rw [hr, hXn]; positivity
  have hr1 : r < 1 := by
    rw [hr, hXn, ← div_eq_mul_inv, div_lt_one hbpos]; exact hlt
  have hes : ∀ k, Multiset.card β < k → β.esymm k = 0 := by
    intro k hk
    simp [Multiset.esymm, Multiset.powersetCard_eq_empty _ hk]
  set d := Multiset.card β with hd
  set p : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * β.esymm k * X ^ k with hp
  have hpz : ∀ k ∉ Finset.range (d + 1), p k = 0 := by
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [hp, hes k (by omega)]
  have hpsum : ∑ k ∈ Finset.range (d + 1), p k = 0 := by
    have h1 := congrArg (Polynomial.eval b) (Multiset.prod_X_sub_X_eq_sum_esymm β)
    rw [Polynomial.eval_multiset_prod, Polynomial.eval_finset_sum] at h1
    have hz : (Multiset.map (Polynomial.eval b)
        (Multiset.map (fun t => Polynomial.X - Polynomial.C t) β)).prod = 0 := by
      apply Multiset.prod_eq_zero
      rw [Multiset.map_map]
      exact Multiset.mem_map.mpr ⟨b, hb, by simp⟩
    rw [hz] at h1
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one,
      Polynomial.eval_C, Polynomial.eval_X] at h1
    have h2 : ∑ k ∈ Finset.range (d + 1), p k
        = X ^ d * ∑ j ∈ Finset.range (d + 1), (-1 : ℂ) ^ j * (β.esymm j * b ^ (d - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkd : k ≤ d := by rw [Finset.mem_range] at hk; omega
      have hXb : X ^ (d - k) * b ^ (d - k) = 1 := by
        rw [← mul_pow, hX, inv_mul_cancel₀ hb0, one_pow]
      have : X ^ d = X ^ k * X ^ (d - k) := by rw [← pow_add, Nat.add_sub_cancel' hkd]
      simp only [hp]
      rw [this]
      linear_combination (-1 : ℂ) ^ k * β.esymm k * X ^ k * hXb.symm
    rw [h2, ← h1, mul_zero]
  have hpsumm : Summable (fun k => ‖p k‖) :=
    summable_of_ne_finset_zero (s := Finset.range (d + 1)) (fun k hk => by simp [hpz k hk])
  have hptsum : ∑' k, p k = 0 := by
    rw [tsum_eq_sum (s := Finset.range (d + 1)) hpz, hpsum]
  set q : ℕ → ℂ := fun n => a n * X ^ n with hq
  have hgeo : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ m * r ^ n) := by
    have h0 : Summable (fun n : ℕ => (n : ℝ) ^ m * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one m (by rw [Real.norm_eq_abs, abs_of_pos hrpos]; exact hr1)
    have h1 := (summable_nat_add_iff 1).mpr h0
    have h2 := h1.mul_left r⁻¹
    refine h2.congr (fun n => ?_)
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  have hqsumm : Summable (fun n => ‖q n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hgeo.mul_left C)
    simp only [hq, norm_mul, norm_pow]
    calc ‖a n‖ * ‖X‖ ^ n ≤ C * ((n : ℝ) + 1) ^ m * B ^ n * ‖X‖ ^ n :=
          mul_le_mul_of_nonneg_right (hgrow n) (by positivity)
      _ = C * (((n : ℝ) + 1) ^ m * r ^ n) := by rw [hr, mul_pow]; ring
  have hcauchy := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hpsumm hqsumm
  rw [hptsum, zero_mul] at hcauchy
  have hterm : ∀ n, ∑ k ∈ Finset.range (n + 1), p k * q (n - k)
      = X ^ n * ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) := by
    intro n
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by rw [Finset.mem_range] at hk; omega
    have : X ^ n = X ^ k * X ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hkn]
    simp only [hp, hq]
    rw [this]; ring
  have hone : ∑' n, ∑ k ∈ Finset.range (n + 1), p k * q (n - k) = 1 := by
    rw [tsum_eq_single 0]
    · simp [hp, hq, ha0, Multiset.esymm, Multiset.powersetCard_zero_left]
    · intro n hn
      rw [hterm n, hrec n (Nat.one_le_iff_ne_zero.mpr hn), mul_zero]
  rw [hone] at hcauchy
  exact zero_ne_one hcauchy

end GlobalTheory
