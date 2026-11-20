import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorOrderHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.TorRef.phiDivO | exact GlobalTheory.TorRef.phiDivO | (intros; apply GlobalTheory.TorRef.phiDivO <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.phi_divisor_order_holds : PhiDivOSt := by
  first | exact @GlobalTheory.TorRef.phiDivO | exact GlobalTheory.TorRef.phiDivO | (intros; apply GlobalTheory.TorRef.phiDivO <;> assumption)
