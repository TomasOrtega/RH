import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsPsh
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PshMean
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Metric Real

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem ChartImagMean.proof : ChartImagMean.Statement := by
  intro D z w hdisc j k
  have hball : ∀ ζ ∈ closedBall (0 : ℂ) 1, z + ζ • w ∈ D.Ustar := fun ζ hζ =>
    hdisc ζ (mem_closedBall_zero_iff.mp hζ)

  have hY : ∀ x, D.Y x j k = (D.τ0 x j k).im +
      ∑ i, (-(2 * π)⁻¹ * D.B i j k) * Real.log ‖x (Fin.castLE D.a_le i)‖ := by
    intro x
    simp only [PeriodChartData.Y, chartImag, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.map_apply, cuspTime, cuspCoord, smul_eq_mul, Real.log_inv]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

  have hτ : AnalyticOnNhd ℂ (fun ζ : ℂ => D.τ0 (z + ζ • w) j k) (closedBall 0 1) := by
    intro ζ hζ
    exact AnalyticAt.comp (g := fun x => D.τ0 x j k) (f := fun ζ : ℂ => z + ζ • w)
      (D.τ0_analytic j k _ (hball ζ hζ).1)
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  have hc : ∀ i, AnalyticOnNhd ℂ
      (fun ζ : ℂ => z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)) (closedBall 0 1) :=
    fun i ζ _ => analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hcne : ∀ i, ∀ ζ ∈ closedBall (0 : ℂ) 1,
      z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i) ≠ 0 := by
    intro i ζ hζ
    have := (hball ζ hζ).2 i
    simpa [cuspCoord] using this

  have hτc : ContinuousOn (fun ζ : ℂ => (D.τ0 (z + ζ • w) j k).im) (closedBall 0 1) :=
    Complex.continuous_im.comp_continuousOn hτ.continuousOn
  have hlc : ∀ i, ContinuousOn
      (fun ζ : ℂ => (-(2 * π)⁻¹ * D.B i j k) *
        Real.log ‖z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)‖) (closedBall 0 1) := by
    intro i
    refine continuousOn_const.mul ((hc i).continuousOn.norm.log fun ζ hζ => ?_)
    exact norm_ne_zero_iff.mpr (hcne i ζ hζ)
  have hint : ∀ {f : ℂ → ℝ}, ContinuousOn f (closedBall 0 1) → CircleIntegrable f 0 1 :=
    fun hf => (hf.mono sphere_subset_closedBall).circleIntegrable zero_le_one
  have hfun : (fun ζ : ℂ => D.Y (z + ζ • w) j k) = fun ζ : ℂ =>
      (D.τ0 (z + ζ • w) j k).im + ∑ i, (-(2 * π)⁻¹ * D.B i j k) *
        Real.log ‖z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)‖ := by
    funext ζ
    rw [hY]
    simp
  rw [hfun, circleAverage_fun_add (hint hτc)
    (hint (continuousOn_finsetSum _ fun i _ => hlc i)),
    circleAverage_fun_sum fun i _ => hint (hlc i), MCPsh.circleAverage_im_of_analytic hτ, hY z]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hs : circleAverage (fun ζ : ℂ => (-(2 * π)⁻¹ * D.B i j k) *
        Real.log ‖z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)‖) 0 1 =
        (-(2 * π)⁻¹ * D.B i j k) * circleAverage (fun ζ : ℂ =>
        Real.log ‖z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)‖) 0 1 :=
      circleAverage_fun_smul (E := ℝ) (𝕜 := ℝ) (a := -(2 * π)⁻¹ * D.B i j k)
        (f := fun ζ : ℂ => Real.log ‖z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)‖)
    rw [hs, MCPsh.circleAverage_log_norm_of_ne_zero (hc i) (hcne i)]
    simp

end

end GroundTheory.Heights₂.Heights
