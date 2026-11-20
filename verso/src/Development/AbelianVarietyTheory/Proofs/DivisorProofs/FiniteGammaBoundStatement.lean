import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGammaBound
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteGammaBound.lean&line=289#L289)
-/
theorem _root_.GlobalTheory.T.finite_gamma_bound : GlobalTheory.FunPr.Hypotheses₂ → FinGamK := by
  first | exact @GlobalTheory.GamLoss.finGamK | exact GlobalTheory.GamLoss.finGamK | (intros; apply GlobalTheory.GamLoss.finGamK <;> assumption)
