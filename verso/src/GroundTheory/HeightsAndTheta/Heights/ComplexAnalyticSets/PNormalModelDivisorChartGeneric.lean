import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelGoodPointGeneric
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelGoodPointChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

/- English proof (translation)
Introduce `n d J u M hJ hd hu`. Take `⟨B, hB, hBd, hgood⟩` from `h₁ n d J u M hJ hd hu`. Conclude with `⟨B, hB, hBd, fun w hw hu0 hwB => h₂ n d J u M w (hgood w hw hu0 hwB)⟩`.
-/
theorem NormalModelDivisorChartGeneric.proof (h₁ : NormalModelGoodPointGeneric.Statement)
    (h₂ : NormalModelGoodPointChart.Statement) : NormalModelDivisorChartGeneric.Statement := by
  intro n d J u M hJ hd hu
  obtain ⟨B, hB, hBd, hgood⟩ := h₁ n d J u M hJ hd hu
  exact ⟨B, hB, hBd, fun w hw hu0 hwB => h₂ n d J u M w (hgood w hw hu0 hwB)⟩

end

end GroundTheory.Heights₂.Heights
