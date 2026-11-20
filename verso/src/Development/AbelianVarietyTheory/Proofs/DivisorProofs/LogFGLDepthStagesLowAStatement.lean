import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFGLDepthStagesLowA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLogFGLDepthStagesLowA.lean&line=311#L311)
-/
theorem _root_.GlobalTheory.T.logFGL_depth_stages_lowA : LowAStatement := by
  first | exact @GlobalTheory.DepthStages.lowA_statement | exact GlobalTheory.DepthStages.lowA_statement | (intros; apply GlobalTheory.DepthStages.lowA_statement <;> assumption)
