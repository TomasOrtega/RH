import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HalfGeo.chartSt_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChartResult.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.chart_result : ChartSt := by
  first | exact @GlobalTheory.HalfGeo.chartSt_holds | exact GlobalTheory.HalfGeo.chartSt_holds | (intros; apply GlobalTheory.HalfGeo.chartSt_holds <;> assumption)
