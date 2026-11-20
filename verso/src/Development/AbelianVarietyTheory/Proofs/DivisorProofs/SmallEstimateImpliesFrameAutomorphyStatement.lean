import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEstimateImpliesFrameAutomorphy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrameAut.autSt_of_smallSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmallEstimateImpliesFrameAutomorphy.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.small_estimate_implies_frame_automorphy : GlobalTheory.ExpTie.SmallSt → GlobalTheory.FrameAut.AutSt := by
  first | exact @GlobalTheory.FrameAut.autSt_of_smallSt | exact GlobalTheory.FrameAut.autSt_of_smallSt | (intros; apply GlobalTheory.FrameAut.autSt_of_smallSt <;> assumption)
