import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

noncomputable section

/- English proof (translation)
Rewrite using `[← LinearMap.normDet_sq L]`. Use `push_cast`. Conclude with `Real.sqrt_sq (LinearMap.normDet_nonneg L)`.
-/
theorem AreaLinear.sqrt_det_adjoint_comp_eq_normDet {k m : ℕ}
    (L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    √(LinearMap.det (LinearMap.adjoint L ∘ₗ L)) = L.normDet := by
  rw [← LinearMap.normDet_sq L]
  push_cast
  exact Real.sqrt_sq (LinearMap.normDet_nonneg L)

/- English proof (translation)
Introduce `k m L _ A`. Establish `h` using `LinearMap.hausdorffMeasure_image L A`. Rewrite `h` using `[finrank_euclideanSpace_fin]`. Rewrite using `[h, AreaLinear.sqrt_det_adjoint_comp_eq_normDet]`.
-/
theorem AreaLinear.proof : AreaLinear.Statement := by
  intro k m L _ A
  have h := LinearMap.hausdorffMeasure_image L A
  rw [finrank_euclideanSpace_fin] at h
  rw [h, AreaLinear.sqrt_det_adjoint_comp_eq_normDet]

end

end GroundTheory.Heights₂.Heights
