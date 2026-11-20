import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorIntegralHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.TorRef.phiDivZSt | exact GlobalTheory.TorRef.phiDivZSt | (intros; apply GlobalTheory.TorRef.phiDivZSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.phi_divisor_integral_holds : PhiDivZSt := by
  first | exact @GlobalTheory.TorRef.phiDivZSt | exact GlobalTheory.TorRef.phiDivZSt | (intros; apply GlobalTheory.TorRef.phiDivZSt <;> assumption)
