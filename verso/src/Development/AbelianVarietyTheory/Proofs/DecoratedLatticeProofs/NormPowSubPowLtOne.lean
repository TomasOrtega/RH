import Mathlib

namespace GlobalTheory.UltrametricPowerDifference

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `hsplit : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n` using `by ring`. Rewrite using `[hsplit]`.

Use `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ha) ih`. Rewrite using `[norm_mul, norm_pow]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hb)) hab`.
-/
theorem norm_pow_sub_pow_lt_one {K : Type} [NormedField K] [IsUltrametricDist K] (a b : K)
    (ha : ‖a‖ ≤ (1 : ℝ)) (hb : ‖b‖ ≤ (1 : ℝ)) (hab : ‖a - b‖ < (1 : ℝ)) (n : ℕ) :
    ‖a ^ n - b ^ n‖ < (1 : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [hsplit]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ha) ih
    · rw [norm_mul, norm_pow]
      exact lt_of_le_of_lt
        (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hb)) hab

end GlobalTheory.UltrametricPowerDifference
