import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FConnectingStatement.lean&line=182#L182)
-/
theorem _root_.GlobalTheory.T.ConnectingStatement : BridgeSt := by
  first | exact @GlobalTheory.DetHT.Bridge.bridge | exact GlobalTheory.DetHT.Bridge.bridge | (intros; apply GlobalTheory.DetHT.Bridge.bridge <;> assumption)
