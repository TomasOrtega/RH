import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLinearRightLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumEqZeroOfMultilin
open GlobalTheory.RowClaim GlobalTheory.ConnectionLinear
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.lastSeesaw_linear_right_largeDepth : Big fun ch => GlobalTheory.ConnectionLinear.LastLin ch 1 := by
  first | exact @GlobalTheory.ConnectionLinear.big_lastLin_one | exact GlobalTheory.ConnectionLinear.big_lastLin_one | (intros; apply GlobalTheory.ConnectionLinear.big_lastLin_one <;> assumption)
