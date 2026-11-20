import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PshCore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCPsh

open Metric Real

noncomputable section

/- English proof (translation)
Apply `DiffContOnCl.circleAverage` to reduce the goal to its premises. Apply `DifferentiableOn.diffContOnCl` to reduce the goal to its premises. Rewrite using `[closure_ball _ (by norm_num : |(1:ℝ)| ≠ 0), abs_one]`. Conclude with `hh.differentiableOn`.
-/
theorem circleAverage_of_analytic {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    circleAverage h 0 1 = h 0 := by
  apply DiffContOnCl.circleAverage
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball _ (by norm_num : |(1:ℝ)| ≠ 0), abs_one]
  exact hh.differentiableOn

/- English proof (translation)
The claim follows from `(hh.continuousOn.mono sphere_subset_closedBall).circleIntegrable zero_le_one`.
-/
theorem circleIntegrable_of_analytic {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    CircleIntegrable h 0 1 :=
  (hh.continuousOn.mono sphere_subset_closedBall).circleIntegrable zero_le_one

/- English proof (translation)
Use `Complex.imCLM.circleAverage_comp_comm (circleIntegrable_of_analytic hh)` as an intermediate fact. Rewrite `this` using `[circleAverage_of_analytic hh]`. Simplify `this` using `[Function.comp_def]`.
-/
theorem circleAverage_im_of_analytic {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    circleAverage (fun ζ => (h ζ).im) 0 1 = (h 0).im := by
  have := Complex.imCLM.circleAverage_comp_comm (circleIntegrable_of_analytic hh)
  rw [circleAverage_of_analytic hh] at this
  simpa [Function.comp_def] using this

/- English proof (translation)
Establish `hh' : AnalyticOnNhd ℂ h (closedBall 0 |(1 : ℝ)|)` using `by simpa using hh`. Rewrite using `[hh'.circleAverage_log_norm one_ne_zero (hne 0 (mem_closedBall_self zero_le_one))]`. Establish `hzero : ∀ u : ℂ, (MeromorphicOn.divisor h (closedBall 0 |(1:ℝ)|) u : ℝ) * Real.log (1 * ‖(0:ℂ) - u‖⁻¹) = 0`. Introduce `u`. Distinguish the cases in `hu : u ∈ closedBall (0:ℂ) |(1:ℝ)|`.

Establish `hu' : u ∈ closedBall (0:ℂ) 1` using `by simpa using hu`. Rewrite using `[MeromorphicOn.AnalyticOnNhd.divisor_apply hh' hu, (hh' u hu).analyticOrderAt_eq_zero.mpr (hne u hu')]`. Simplify using the standard rewrite rules. Rewrite using `[Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]`. Simplify using the standard rewrite rules.

Establish `hz2 : ∀ u : ℂ, -((MeromorphicOn.divisor h (closedBall 0 |(1:ℝ)|) u : ℝ) * Real.log ‖u‖) = 0`. Introduce `u`. Use `hzero u` as an intermediate fact. Simplify using `only [one_mul, zero_sub, norm_neg, Real.log_inv, mul_neg] at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `only [one_mul, zero_sub, norm_neg, Real.log_inv, mul_neg, hz2, finsum_zero, zero_add]`.
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
