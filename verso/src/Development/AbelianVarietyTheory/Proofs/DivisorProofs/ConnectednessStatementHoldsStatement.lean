import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectednessStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FConnectednessStatementHolds.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.connectedness_statement_holds : GlobalTheory.CovTop.Hypotheses2 → ConnSt := by
  first | exact @GlobalTheory.FlatModel.connected_of_hypotheses | exact GlobalTheory.FlatModel.connected_of_hypotheses | (intros; apply GlobalTheory.FlatModel.connected_of_hypotheses <;> assumption)
