import Mathlib

namespace GlobalTheory.IsotropicVectorExistence

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `e : z ^ (2 ^ (k + 1)) - 1 = (z ^ (2 ^ k) - 1) * (z ^ (2 ^ k) + 1)`. Rewrite using `[show 2 ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k, pow_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (3 / 2 : ℝ) ≤ ‖z ^ (2 ^ k) + 1‖`. Establish `h3 : (2 : ℂ) = (z ^ (2 ^ k) + 1) - (z ^ (2 ^ k) - 1)` using `by ring`. Establish `h4 : ‖(2 : ℂ)‖ ≤ ‖z ^ (2 ^ k) + 1‖ + ‖z ^ (2 ^ k) - 1‖`. Rewrite using `[h3]`.

Conclude with `norm_sub_le _ _`. Establish `h5 : ‖(2 : ℂ)‖ = 2` using `by norm_num`. Establish `h6` using `h (2 ^ k)`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[e, norm_mul, pow_succ]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem key {z : ℂ} (k : ℕ) (h : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : z ^ (2 ^ (k + 1)) - 1 = (z ^ (2 ^ k) - 1) * (z ^ (2 ^ k) + 1) := by
      rw [show 2 ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k, pow_mul]; ring
    have h2 : (3 / 2 : ℝ) ≤ ‖z ^ (2 ^ k) + 1‖ := by
      have h3 : (2 : ℂ) = (z ^ (2 ^ k) + 1) - (z ^ (2 ^ k) - 1) := by ring
      have h4 : ‖(2 : ℂ)‖ ≤ ‖z ^ (2 ^ k) + 1‖ + ‖z ^ (2 ^ k) - 1‖ := by
        rw [h3]; exact norm_sub_le _ _
      have h5 : ‖(2 : ℂ)‖ = 2 := by norm_num
      have h6 := h (2 ^ k)
      linarith
    rw [e, norm_mul, pow_succ]
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = ((3 / 2) ^ k * ‖z - 1‖) * (3 / 2) := by ring
      _ ≤ ‖z ^ (2 ^ k) - 1‖ * ‖z ^ (2 ^ k) + 1‖ :=
        mul_le_mul ih h2 (by norm_num) (norm_nonneg _)

/- English proof (translation)
Introduce `z h`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖z - 1‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hne)`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)`. Rewrite `hk` using `[div_lt_iff₀ (by positivity)]`.

Establish `a` using `key k h`. Establish `b` using `h (2 ^ k)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ (by positivity)] at hk
  have a := key k h
  have b := h (2 ^ k)
  nlinarith

end GlobalTheory.IsotropicVectorExistence
