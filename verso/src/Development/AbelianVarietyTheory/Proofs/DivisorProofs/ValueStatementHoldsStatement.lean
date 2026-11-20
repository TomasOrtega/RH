import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FValueStatementHolds.lean&line=244#L244)
-/
theorem _root_.GlobalTheory.T.value_statement_holds : ValueSt := by
  first | exact @GlobalTheory.FlatModel.valueSt | exact GlobalTheory.FlatModel.valueSt | (intros; apply GlobalTheory.FlatModel.valueSt <;> assumption)
