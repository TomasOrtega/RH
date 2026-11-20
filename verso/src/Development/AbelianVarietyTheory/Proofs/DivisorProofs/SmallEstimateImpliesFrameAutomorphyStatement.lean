import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEstimateImpliesFrameAutomorphy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.FrameAut.autSt_of_smallSt | exact GlobalTheory.FrameAut.autSt_of_smallSt | (intros; apply GlobalTheory.FrameAut.autSt_of_smallSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.small_estimate_implies_frame_automorphy : GlobalTheory.ExpTie.SmallSt → GlobalTheory.FrameAut.AutSt := by
  first | exact @GlobalTheory.FrameAut.autSt_of_smallSt | exact GlobalTheory.FrameAut.autSt_of_smallSt | (intros; apply GlobalTheory.FrameAut.autSt_of_smallSt <;> assumption)
