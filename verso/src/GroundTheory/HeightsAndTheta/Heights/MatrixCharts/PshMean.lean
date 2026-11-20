import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PshCore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCPsh

open Metric Real

noncomputable section

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem circleAverage_of_analytic {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    circleAverage h 0 1 = h 0 := by
  apply DiffContOnCl.circleAverage
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball _ (by norm_num : |(1:ℝ)| ≠ 0), abs_one]
  exact hh.differentiableOn

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem circleIntegrable_of_analytic {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    CircleIntegrable h 0 1 :=
  (hh.continuousOn.mono sphere_subset_closedBall).circleIntegrable zero_le_one

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem circleAverage_im_of_analytic {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    circleAverage (fun ζ => (h ζ).im) 0 1 = (h 0).im := by
  have := Complex.imCLM.circleAverage_comp_comm (circleIntegrable_of_analytic hh)
  rw [circleAverage_of_analytic hh] at this
  simpa [Function.comp_def] using this

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using the standard rewrite rules.
-/
theorem circleAverage_log_norm_of_ne_zero {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1))
    (hne : ∀ ζ ∈ closedBall (0:ℂ) 1, h ζ ≠ 0) :
    circleAverage (fun ζ => Real.log ‖h ζ‖) 0 1 = Real.log ‖h 0‖ := by
  have hh' : AnalyticOnNhd ℂ h (closedBall 0 |(1 : ℝ)|) := by simpa using hh
  rw [hh'.circleAverage_log_norm one_ne_zero (hne 0 (mem_closedBall_self zero_le_one))]
  have hzero : ∀ u : ℂ, (MeromorphicOn.divisor h (closedBall 0 |(1:ℝ)|) u : ℝ) *
      Real.log (1 * ‖(0:ℂ) - u‖⁻¹) = 0 := by
    intro u
    by_cases hu : u ∈ closedBall (0:ℂ) |(1:ℝ)|
    · have hu' : u ∈ closedBall (0:ℂ) 1 := by simpa using hu
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hh' hu, (hh' u hu).analyticOrderAt_eq_zero.mpr (hne u hu')]
      simp
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
      simp
  have hz2 : ∀ u : ℂ, -((MeromorphicOn.divisor h (closedBall 0 |(1:ℝ)|) u : ℝ) * Real.log ‖u‖) = 0 := by
    intro u
    have := hzero u
    simp only [one_mul, zero_sub, norm_neg, Real.log_inv, mul_neg] at this
    linarith
  simp only [one_mul, zero_sub, norm_neg, Real.log_inv, mul_neg, hz2, finsum_zero, zero_add]

end

end GroundTheory.Heights₂.Heights.MCPsh
