import Mathlib

/- English proof (translation)
Introduce `K _ _ x y hx hy e`. Proceed by induction on `e with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `h : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n` using `by ring`.

Rewrite using `[h]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) hx).trans ih`. Rewrite using `[norm_mul, norm_pow]`.

Conclude with `mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hy)`.
-/
theorem UpperTheory.Reformulated.B.Qi18.norm_pow_sub_pow_le.{u_1} :
    ∀ {K : Type u_1} [inst : NormedField K]
    [IsUltrametricDist K] (x y : K), ‖x‖ ≤ (1 : ℝ) → ‖y‖ ≤ (1 : ℝ) → ∀ (e : ℕ), ‖x ^ e - y ^ e‖ ≤ ‖x - y‖ := by
  intro K _ _ x y hx hy e
  induction e with
  | zero => simp
  | succ n ih =>
    have h : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans ih
    · rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hy)
