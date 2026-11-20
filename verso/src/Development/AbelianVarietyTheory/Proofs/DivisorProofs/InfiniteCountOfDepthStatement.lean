import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteCountOfDepth
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SumCount.infCountK` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FInfiniteCountOfDepth.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.infinite_count_of_depth : GlobalTheory.FunPr.Hypotheses₂ → DepthK → InfCountK := by
  first | exact @GlobalTheory.SumCount.infCountK | exact GlobalTheory.SumCount.infCountK | (intros; apply GlobalTheory.SumCount.infCountK <;> assumption)
