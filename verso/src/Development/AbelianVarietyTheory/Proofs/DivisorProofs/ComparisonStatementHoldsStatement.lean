import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FComparisonStatementHolds.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.comparison_statement_holds : CmpSt := by
  first | exact @GlobalTheory.FlatModel.cmpSt_holds | exact GlobalTheory.FlatModel.cmpSt_holds | (intros; apply GlobalTheory.FlatModel.cmpSt_holds <;> assumption)
