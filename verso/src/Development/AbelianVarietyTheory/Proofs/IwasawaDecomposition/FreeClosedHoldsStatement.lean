import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FreeClosedHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorRef.freeClosedSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFreeClosedHolds.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.free_closed_holds : FreeClosedSt := by
  first | exact @GlobalTheory.TorRef.freeClosedSt | exact GlobalTheory.TorRef.freeClosedSt | (intros; apply GlobalTheory.TorRef.freeClosedSt <;> assumption)
