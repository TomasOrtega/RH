import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBoundStatementHolds.lean&line=193#L193)
-/
theorem _root_.GlobalTheory.T.bound_statement_holds : BoundSt := by
  first | exact @GlobalTheory.FlatModel.boundSt | exact GlobalTheory.FlatModel.boundSt | (intros; apply GlobalTheory.FlatModel.boundSt <;> assumption)
