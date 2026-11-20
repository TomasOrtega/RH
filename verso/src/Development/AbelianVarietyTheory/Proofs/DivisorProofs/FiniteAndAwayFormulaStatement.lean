import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAndAwayFormula
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Adopt.finite_and_away_formula` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteAndAwayFormula.lean&line=172#L172)
-/
theorem _root_.GlobalTheory.T.finite_and_away_formula : SetAt → FinK → AwayK → FP @Comparison₂ := by
  first | exact @GlobalTheory.Adopt.finite_and_away_formula | exact GlobalTheory.Adopt.finite_and_away_formula | (intros; apply GlobalTheory.Adopt.finite_and_away_formula <;> assumption)
