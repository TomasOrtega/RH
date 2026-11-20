import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsExistAffineZeroSection
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
open GlobalTheory.AnPer
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AnPer.periods_exist` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPeriodsExistAffineZeroSection.lean&line=157#L157)
-/
theorem _root_.GlobalTheory.T.periods_exist_affine_zero_section : PExist := by
  first | exact @GlobalTheory.AnPer.periods_exist | exact GlobalTheory.AnPer.periods_exist | (intros; apply GlobalTheory.AnPer.periods_exist <;> assumption)
