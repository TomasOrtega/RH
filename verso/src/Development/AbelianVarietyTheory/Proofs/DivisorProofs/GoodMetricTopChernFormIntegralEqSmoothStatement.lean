import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricTopChernFormIntegralEqSmooth
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GoodTopChernForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GoodTop.goodTopChernForm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGoodMetricTopChernFormIntegralEqSmooth.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.goodMetric_topChernForm_integral_eq_smooth : GlobalTheory.Published.GoodTopChernForm := by
  first | exact @GlobalTheory.GoodTop.goodTopChernForm | exact GlobalTheory.GoodTop.goodTopChernForm | (intros; apply GlobalTheory.GoodTop.goodTopChernForm <;> assumption)
