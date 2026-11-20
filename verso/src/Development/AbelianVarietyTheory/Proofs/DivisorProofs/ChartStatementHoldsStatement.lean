import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatModel.chartSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChartStatementHolds.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.chart_statement_holds : ChartSt := by
  first | exact @GlobalTheory.FlatModel.chartSt | exact GlobalTheory.FlatModel.chartSt | (intros; apply GlobalTheory.FlatModel.chartSt <;> assumption)
