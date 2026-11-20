import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOfSumBound
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DepthUnf.depthK_of_sumOKK₂` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDepthOfSumBound.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.depth_of_sum_bound : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → DepthK := by
  first | exact @GlobalTheory.DepthUnf.depthK_of_sumOKK₂ | exact GlobalTheory.DepthUnf.depthK_of_sumOKK₂ | (intros; apply GlobalTheory.DepthUnf.depthK_of_sumOKK₂ <;> assumption)
