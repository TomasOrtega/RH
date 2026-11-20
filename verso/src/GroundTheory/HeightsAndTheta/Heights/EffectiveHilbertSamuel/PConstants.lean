import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

/- English proof (translation)
Establish `hpi` using `Real.pi_lt_d2`. Establish `hpi0` using `Real.pi_gt_three`. Rewrite using `[← Real.log_mul (by norm_num) (by positivity)]`. Rewrite using `[Real.log_le_iff_le_exp (by positivity)]`. Establish `hsplit : exp 7.6 = exp 1 ^ 7 * exp 0.6`.

Rewrite using `[← Real.exp_nat_mul, ← Real.exp_add]`. Use `congr 1`. Evaluate the numerical expressions. Rewrite using `[hsplit]`. Establish `h7 : (2.7182818283 : ℝ) ^ 7 ≤ exp 1 ^ 7` using `pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 7`.

Establish `h06 : (1 + 0.6 + 0.6 ^ 2 / 2 : ℝ) ≤ exp 0.6` using `Real.quadratic_le_exp_of_nonneg (by norm_num)`. Establish `hpos : (0 : ℝ) ≤ (2.7182818283 : ℝ) ^ 7` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem log_add_log_two_pi_le : log 280 + log (2 * π) ≤ 7.6 := by
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_gt_three
  rw [← Real.log_mul (by norm_num) (by positivity)]
  rw [Real.log_le_iff_le_exp (by positivity)]
  have hsplit : exp 7.6 = exp 1 ^ 7 * exp 0.6 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  rw [hsplit]
  have h7 : (2.7182818283 : ℝ) ^ 7 ≤ exp 1 ^ 7 :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 7
  have h06 : (1 + 0.6 + 0.6 ^ 2 / 2 : ℝ) ≤ exp 0.6 :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have hpos : (0 : ℝ) ≤ (2.7182818283 : ℝ) ^ 7 := by positivity
  calc 280 * (2 * π) ≤ (2.7182818283 : ℝ) ^ 7 * (1 + 0.6 + 0.6 ^ 2 / 2) := by
        norm_num; nlinarith
    _ ≤ exp 1 ^ 7 * exp 0.6 :=
        mul_le_mul h7 h06 (by norm_num) (by positivity)

/- English proof (translation)
Establish `h` using `log_add_log_two_pi_le`. Establish `h280 : 0 ≤ log (280 : ℝ)` using `Real.log_nonneg (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_two_pi_le : log (2 * π) ≤ 7.6 := by
  have h := log_add_log_two_pi_le
  have h280 : 0 ≤ log (280 : ℝ) := Real.log_nonneg (by norm_num)
  linarith

/- English proof (translation)
Establish `h1` using `log_add_log_two_pi_le`. Establish `h2` using `log_two_pi_le`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ D - 1)]`.
-/
theorem half_log_add_le (D : ℝ) (hD : 1 ≤ D) :
    (1 / 2) * (log 280 + D * log (2 * π)) ≤ 3.8 * D := by
  have h1 := log_add_log_two_pi_le
  have h2 := log_two_pi_le
  nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ D - 1)]

/- English proof (translation)
Establish `h : log ((2 : ℝ) ^ 26) ≤ log ρ` using `Real.log_le_log (by positivity) hρ`. Rewrite `h` using `[Real.log_pow]`. Use `Real.log_two_gt_d9` as an intermediate fact. Move the coercions through the operations in `at h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem seven_point_six_le_log (ρ : ℝ) (hρ : 2 ^ 26 ≤ ρ) : 7.6 ≤ log ρ := by
  have h : log ((2 : ℝ) ^ 26) ≤ log ρ := Real.log_le_log (by positivity) hρ
  rw [Real.log_pow] at h
  have := Real.log_two_gt_d9
  push_cast at h
  linarith

/- English proof (translation)
Establish `h` using `seven_point_six_le_log ρ hρ`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h hD]`.
-/
theorem three_point_eight_le_half_log (D ρ : ℝ) (hD : 0 ≤ D) (hρ : 2 ^ 26 ≤ ρ) :
    3.8 * D ≤ (D / 2) * log ρ := by
  have h := seven_point_six_le_log ρ hρ
  nlinarith [mul_le_mul_of_nonneg_left h hD]

/- English proof (translation)
Assemble the required witnesses or components as `⟨half_log_add_le D hD, three_point_eight_le_half_log D ρ (by linarith) hρ⟩`.
-/
theorem half_log_add_le_half_log (D ρ : ℝ) (hD : 1 ≤ D) (hρ : 2 ^ 26 ≤ ρ) :
    (1 / 2) * (log 280 + D * log (2 * π)) ≤ 3.8 * D ∧ 3.8 * D ≤ (D / 2) * log ρ :=
  ⟨half_log_add_le D hD, three_point_eight_le_half_log D ρ (by linarith) hρ⟩

def vanishingOrderBound (T D N : ℝ) : ℝ := T + 2 * D + 4 + N

end GroundTheory.Heights₂.Heights
