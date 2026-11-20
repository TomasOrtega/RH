import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictionStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatModel.restrictSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRestrictionStatementHolds.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.restriction_statement_holds : RestrictSt := by
  first | exact @GlobalTheory.FlatModel.restrictSt | exact GlobalTheory.FlatModel.restrictSt | (intros; apply GlobalTheory.FlatModel.restrictSt <;> assumption)
