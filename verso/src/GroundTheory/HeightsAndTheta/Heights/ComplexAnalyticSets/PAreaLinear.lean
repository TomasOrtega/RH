import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

noncomputable section

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. A detailed English derivation is pending.
-/
theorem AreaLinear.sqrt_det_adjoint_comp_eq_normDet {k m : ℕ}
    (L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    √(LinearMap.det (LinearMap.adjoint L ∘ₗ L)) = L.normDet := by
  rw [← LinearMap.normDet_sq L]
  push_cast
  exact Real.sqrt_sq (LinearMap.normDet_nonneg L)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem AreaLinear.proof : AreaLinear.Statement := by
  intro k m L _ A
  have h := LinearMap.hausdorffMeasure_image L A
  rw [finrank_euclideanSpace_fin] at h
  rw [h, AreaLinear.sqrt_det_adjoint_comp_eq_normDet]

end

end GroundTheory.Heights₂.Heights
