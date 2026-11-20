import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTensorBound
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FInfiniteTensorBound.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.infinite_tensor_bound : GlobalTheory.FunPr.Hypotheses₂ → InfTensK := by
  first | exact @GlobalTheory.SumSize.infTensK_of_hypotheses | exact GlobalTheory.SumSize.infTensK_of_hypotheses | (intros; apply GlobalTheory.SumSize.infTensK_of_hypotheses <;> assumption)
