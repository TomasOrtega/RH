import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RealDoublingNorm
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.real_doubling_norm : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.RealDoublingNorm := by
  first | exact @GlobalTheory.RealDoubling.realDoublingNorm | exact GlobalTheory.RealDoubling.realDoublingNorm | (intros; apply GlobalTheory.RealDoubling.realDoublingNorm <;> assumption)
