import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsOfDeRhamClassesUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
open GlobalTheory.AnPer
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPeriodsOfDeRhamClassesUnique.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.periods_of_deRham_classes_unique : PUniq := by
  first | exact @GlobalTheory.AnPer.period_unique | exact GlobalTheory.AnPer.period_unique | (intros; apply GlobalTheory.AnPer.period_unique <;> assumption)
