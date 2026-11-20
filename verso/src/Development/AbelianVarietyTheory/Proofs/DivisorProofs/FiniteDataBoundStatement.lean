import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDataBound
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteDataBound.lean&line=236#L236)
-/
theorem _root_.GlobalTheory.T.finite_data_bound : GlobalTheory.FunPr.Hypotheses₂ → FinDatK := by
  first | exact @GlobalTheory.FunDat.finDatK | exact GlobalTheory.FunDat.finDatK | (intros; apply GlobalTheory.FunDat.finDatK <;> assumption)
