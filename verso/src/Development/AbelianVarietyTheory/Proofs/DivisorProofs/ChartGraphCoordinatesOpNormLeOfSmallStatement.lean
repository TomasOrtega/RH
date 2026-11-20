import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartGraphCoordinatesOpNormLeOfSmall
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBottomLeftBlock
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChartGraphCoordinatesOpNormLeOfSmall.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.chartGraphCoordinates_opNorm_le_of_small : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (z : V (nd X)),
    (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 → X.zN (graphCoord X z) ≤ 1 / 50 := by
  first | exact @GlobalTheory.ChartGraph.zN_graphCoord_le | exact GlobalTheory.ChartGraph.zN_graphCoord_le | (intros; apply GlobalTheory.ChartGraph.zN_graphCoord_le <;> assumption)
