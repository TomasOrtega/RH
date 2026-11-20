import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteScalarBounds
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteInfiniteScalarBounds.lean&line=443#L443)
-/
theorem _root_.GlobalTheory.T.finite_infinite_scalar_bounds : GlobalTheory.FunPr.Hypotheses₂ → FinScalK ∧ InfScalK := by
  first | exact @GlobalTheory.ScalAA.finScal_infScal | exact GlobalTheory.ScalAA.finScal_infScal | (intros; apply GlobalTheory.ScalAA.finScal_infScal <;> assumption)
