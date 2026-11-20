import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePairBounds
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FPair.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteInfinitePairBounds.lean&line=144#L144)
-/
theorem _root_.GlobalTheory.T.finite_infinite_pair_bounds : GlobalTheory.FunPr.Hypotheses₂ → FinPairK ∧ InfPairK := by
  first | exact @GlobalTheory.FPair.main | exact GlobalTheory.FPair.main | (intros; apply GlobalTheory.FPair.main <;> assumption)
