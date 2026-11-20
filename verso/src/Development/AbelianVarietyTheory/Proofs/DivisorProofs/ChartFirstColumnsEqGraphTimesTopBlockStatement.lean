import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFirstColumnsEqGraphTimesTopBlock
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBottomLeftBlock
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ChartGraph.cols_graph` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChartFirstColumnsEqGraphTimesTopBlock.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.chart_firstColumns_eq_graph_times_topBlock : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r)
    (z : V (nd X)) (τ : X.Ψ), (chartMatrixTopBlock X z τ).det = 1 ∧ ∀ a : Fin X.p0,
    col (mat (cpt X x z) τ) (Fin.castLE X.p0_le a) =
      ∑ c : Fin X.p0, chartMatrixTopBlock X z τ c a • col (mat (X.xZ x (graphCoord X z)) τ) (Fin.castLE X.p0_le c) := by
  first | exact @GlobalTheory.ChartGraph.cols_graph | exact GlobalTheory.ChartGraph.cols_graph | (intros; apply GlobalTheory.ChartGraph.cols_graph <;> assumption)
