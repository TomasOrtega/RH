import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FreeClosedHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.TorRef.freeClosedSt | exact GlobalTheory.TorRef.freeClosedSt | (intros; apply GlobalTheory.TorRef.freeClosedSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.free_closed_holds : FreeClosedSt := by
  first | exact @GlobalTheory.TorRef.freeClosedSt | exact GlobalTheory.TorRef.freeClosedSt | (intros; apply GlobalTheory.TorRef.freeClosedSt <;> assumption)
