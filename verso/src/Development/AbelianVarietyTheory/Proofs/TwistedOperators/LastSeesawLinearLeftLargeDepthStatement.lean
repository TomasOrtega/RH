import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLinearLeftLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumEqZeroOfMultilin
open GlobalTheory.RowClaim GlobalTheory.ConnectionLinear
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FLastSeesawLinearLeftLargeDepth.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.lastSeesaw_linear_left_largeDepth : Big fun ch => GlobalTheory.ConnectionLinear.LastLin ch 0 := by
  first | exact @GlobalTheory.LastPositionLin.lastLin_zero | exact GlobalTheory.LastPositionLin.lastLin_zero | (intros; apply GlobalTheory.LastPositionLin.lastLin_zero <;> assumption)
