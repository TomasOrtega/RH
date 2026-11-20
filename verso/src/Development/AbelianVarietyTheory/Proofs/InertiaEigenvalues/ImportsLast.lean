import Mathlib

namespace GlobalTheory.PowerDifferenceNormInertiaEigenvalues

universe u_1

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `h : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + y ^ n * (x - y)` using `by ring`. Rewrite using `[h]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) hx).trans ih`. Rewrite using `[norm_mul, norm_pow]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hy)`.
-/
theorem norm_pow_sub_pow_le {C : Type u_1} [NormedField C] [IsUltrametricDist C] {x y : C}
    (hx : ‖x‖ ≤ (1 : ℝ)) (hy : ‖y‖ ≤ (1 : ℝ)) (n : ℕ) : ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + y ^ n * (x - y) := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans ih
    · rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hy)

end GlobalTheory.PowerDifferenceNormInertiaEigenvalues
