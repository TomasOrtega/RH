import Mathlib

open Matrix Finset Real

namespace GlobalTheory

/- English proof (translation)
Establish `h` using `Real.exp_bound hu (n := 5) (by norm_num)`. Establish `h1` using `(abs_le.mp h).1`. Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1`. Evaluate the numerical expressions using `at h1`. Establish `h4 : |u| ^ 4 = u ^ 4`.

Rewrite using `[← abs_pow]; exact abs_of_nonneg (by positivity)`. Establish `h5 : |u| ^ 5 ≤ u ^ 4`. Rewrite using `[← h4, pow_succ]`. Conclude with `mul_le_of_le_one_right (by positivity) hu`. Establish `h6 : -1 ≤ u` using `(abs_le.mp hu).1`.

Establish `h7 : 0 ≤ u ^ 2 * (1 + u)` using `mul_nonneg (sq_nonneg u) (by linarith)`. Establish `h8 : 0 ≤ u ^ 4` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_add_add_sq_div_three_le_exp (u : ℝ) (hu : |u| ≤ 1) :
    1 + u + u ^ 2 / 3 ≤ Real.exp u := by
  have h := Real.exp_bound hu (n := 5) (by norm_num)
  have h1 := (abs_le.mp h).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h4 : |u| ^ 4 = u ^ 4 := by
    rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  have h5 : |u| ^ 5 ≤ u ^ 4 := by
    rw [← h4, pow_succ]
    exact mul_le_of_le_one_right (by positivity) hu
  have h6 : -1 ≤ u := (abs_le.mp hu).1
  have h7 : 0 ≤ u ^ 2 * (1 + u) := mul_nonneg (sq_nonneg u) (by linarith)
  have h8 : 0 ≤ u ^ 4 := by positivity
  nlinarith

/- English proof (translation)
Establish `hp : 0 < 1 + u` using `by linarith`. Use `le_trans ?_ (Real.one_sub_inv_le_log_of_pos hp)` and prove the remaining obligations. Establish `: (1 + u)⁻¹ ≤ 1 - 3 * u / 4`. Rewrite using `[inv_eq_one_div, div_le_iff₀ hp]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem three_mul_div_four_le_log_one_add (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1 / 3) :
    3 * u / 4 ≤ Real.log (1 + u) := by
  have hp : 0 < 1 + u := by linarith
  refine le_trans ?_ (Real.one_sub_inv_le_log_of_pos hp)
  have : (1 + u)⁻¹ ≤ 1 - 3 * u / 4 := by
    rw [inv_eq_one_div, div_le_iff₀ hp]
    nlinarith
  linarith

/- English proof (translation)
Assemble the required witnesses or components as `⟨one_add_add_sq_div_three_le_exp, three_mul_div_four_le_log_one_add⟩`.
-/
theorem exp_quadratic_lower_and_log_linear_lower :
    (∀ u : ℝ, |u| ≤ 1 → 1 + u + u ^ 2 / 3 ≤ Real.exp u) ∧
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 3 → 3 * u / 4 ≤ Real.log (1 + u) :=
  ⟨one_add_add_sq_div_three_le_exp, three_mul_div_four_le_log_one_add⟩

end GlobalTheory
