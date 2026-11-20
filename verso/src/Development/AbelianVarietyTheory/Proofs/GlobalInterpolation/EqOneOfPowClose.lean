import Mathlib

namespace GlobalTheory.EqOneOfPowerClose

open Finset

/- English proof (translation)
Establish `key : ∀ n : ℕ, (n : ℝ) * ‖u - 1‖ ≤ 1`. Introduce `n`. Establish `h1 : ‖∑ k ∈ range n, (u ^ k - 1)‖ ≤ (n : ℝ) / 2`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : (n : ℂ) = ∑ k ∈ range n, u ^ k - ∑ k ∈ range n, (u ^ k - 1)`.

Rewrite using `[sum_sub_distrib]`. Simplify using the standard rewrite rules. Establish `h3 : (n : ℝ) ≤ ‖∑ k ∈ range n, u ^ k‖ + ‖∑ k ∈ range n, (u ^ k - 1)‖`. Use `norm_sub_le (∑ k ∈ range n, u ^ k) (∑ k ∈ range n, (u ^ k - 1))` as an intermediate fact. Rewrite `this` using `[← h2, Complex.norm_natCast]`.

Conclude with `this`. Establish `h4 : ‖∑ k ∈ range n, u ^ k‖ * ‖u - 1‖ < 1 / 2`. Rewrite using `[← norm_mul, geom_sum_mul]`. Conclude with `h n`. Establish `h5 : (n : ℝ) / 2 ≤ ‖∑ k ∈ range n, u ^ k‖` using `by linarith`.

Establish `h6` using `mul_le_mul_of_nonneg_right h5 (norm_nonneg (u - 1))`. Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖u - 1‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hne)`. Take `⟨n, hn⟩` from `exists_nat_gt (1 / ‖u - 1‖)`.

Rewrite `hn` using `[div_lt_iff₀ hpos]`. Combine the linear relations using `[key n]`.
-/
theorem eq_one_of_pow_close {u : ℂ} (h : ∀ n : ℕ, ‖u ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) :
    u = (1 : ℂ) := by
  have key : ∀ n : ℕ, (n : ℝ) * ‖u - 1‖ ≤ 1 := by
    intro n
    have h1 : ‖∑ k ∈ range n, (u ^ k - 1)‖ ≤ (n : ℝ) / 2 := by
      calc ‖∑ k ∈ range n, (u ^ k - 1)‖ ≤ ∑ k ∈ range n, ‖u ^ k - 1‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ range n, (1 / 2 : ℝ) := sum_le_sum fun k _ => (h k).le
        _ = (n : ℝ) / 2 := by simp; ring
    have h2 : (n : ℂ) = ∑ k ∈ range n, u ^ k - ∑ k ∈ range n, (u ^ k - 1) := by
      rw [sum_sub_distrib]; simp
    have h3 : (n : ℝ) ≤ ‖∑ k ∈ range n, u ^ k‖ + ‖∑ k ∈ range n, (u ^ k - 1)‖ := by
      have := norm_sub_le (∑ k ∈ range n, u ^ k) (∑ k ∈ range n, (u ^ k - 1))
      rw [← h2, Complex.norm_natCast] at this
      exact this
    have h4 : ‖∑ k ∈ range n, u ^ k‖ * ‖u - 1‖ < 1 / 2 := by
      rw [← norm_mul, geom_sum_mul]; exact h n
    have h5 : (n : ℝ) / 2 ≤ ‖∑ k ∈ range n, u ^ k‖ := by linarith
    have h6 := mul_le_mul_of_nonneg_right h5 (norm_nonneg (u - 1))
    linarith
  by_contra hne
  have hpos : 0 < ‖u - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ‖u - 1‖)
  rw [div_lt_iff₀ hpos] at hn
  linarith [key n]

end GlobalTheory.EqOneOfPowerClose
