import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsOfSpanAndTaylorClauses
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
open GlobalTheory.AnPer
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGaussManinPeriodsOfSpanAndTaylorClauses.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.gaussManinPeriods_of_span_and_taylor_clauses : PSpan → PTaylor → GlobalTheory.Published.GaussManinPeriods := by
  first | exact @GlobalTheory.AnPer.gaussManinPeriods_of_span_taylor | exact GlobalTheory.AnPer.gaussManinPeriods_of_span_taylor | (intros; apply GlobalTheory.AnPer.gaussManinPeriods_of_span_taylor <;> assumption)
