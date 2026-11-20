import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open scoped ContDiff

/- English proof (translation)
Introduce `X _ D A U g hg j`. Establish `h1 : ContDiffOn ℝ ∞ (g ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)` using `((hg j).contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ`. Establish `h2 : ContDiff ℝ ∞ (fun w : ℂ => ‖w‖ ^ 2)` using `contDiff_norm_sq ℝ`. Conclude with `h2.comp_contDiffOn h1`.
-/
theorem NormSqSmooth.proof : NormSqSmooth.Statement := by
  intro X _ D A U g hg j
  have h1 : ContDiffOn ℝ ∞ (g ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    ((hg j).contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ
  have h2 : ContDiff ℝ ∞ (fun w : ℂ => ‖w‖ ^ 2) := contDiff_norm_sq ℝ
  exact h2.comp_contDiffOn h1

end GroundTheory.Heights₂.Heights.AnalyticLimit
