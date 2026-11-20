import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem AnalyticDerivBound.proof : AnalyticDerivBound.Statement := by
  intro E _ _ f U K hU hf hK hKU
  have hcd : ContDiffOn ℂ 1 f U := hf.contDiffOn hU.uniqueDiffOn
  have hf' : ContinuousOn (fderiv ℂ f) U := hcd.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn (hcd.continuousOn.mono hKU)
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn (hf'.mono hKU)
  refine ⟨max (max C₁ C₂) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx => ?_⟩
  have hd : DifferentiableAt ℂ f x := (hf x (hKU hx)).differentiableAt
  refine ⟨hd.restrictScalars ℝ, ?_, ?_⟩
  · exact (hC₁ x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
  · rw [hd.fderiv_restrictScalars ℝ, ContinuousLinearMap.norm_restrictScalars]
    exact (hC₂ x hx).trans ((le_max_right _ _).trans (le_max_left _ _))

end GroundTheory.Heights₂.Heights
