import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphyFromSmallExponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.automorphy_from_small_exponent : GlobalTheory.ExpTie.SmallSt → GlobalTheory.FrameAut.AutSt := by
  first | exact @GlobalTheory.FrameAut.autSt | exact GlobalTheory.FrameAut.autSt | (intros; apply GlobalTheory.FrameAut.autSt <;> assumption)
