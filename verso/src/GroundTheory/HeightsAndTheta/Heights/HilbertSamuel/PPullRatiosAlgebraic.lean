import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullGradedAlgebraic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y D e L hy he hL hz`. Take `⟨N, hN⟩` from `h₁ K ι Ω y D L hz`. Conclude with `h₃ K ι Ω y D e L (fun k => e k + N * Fintype.card (ι k)) hy he hL (fun d g hg hd => h₂ K ι Ω y D e L N hy hL hN d g hg hd)`.
-/
theorem PullRatiosAlgebraic.proof (h₁ : PullConeNull.Statement) (h₂ : PullConeDegree.Statement)
    (h₃ : PullGradedAlgebraic.Statement) : PullRatiosAlgebraic.Statement := by
  intro K _ ι _ Ω _ _ y D e L hy he hL hz
  obtain ⟨N, hN⟩ := h₁ K ι Ω y D L hz
  exact h₃ K ι Ω y D e L (fun k => e k + N * Fintype.card (ι k)) hy he hL
    (fun d g hg hd => h₂ K ι Ω y D e L N hy hL hN d g hg hd)

end GroundTheory.Heights₂.Heights.HilbertSamuel
