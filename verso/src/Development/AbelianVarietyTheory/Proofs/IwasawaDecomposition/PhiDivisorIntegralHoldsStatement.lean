import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorIntegralHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPhiDivisorIntegralHolds.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.phi_divisor_integral_holds : PhiDivZSt := by
  first | exact @GlobalTheory.TorRef.phiDivZSt | exact GlobalTheory.TorRef.phiDivZSt | (intros; apply GlobalTheory.TorRef.phiDivZSt <;> assumption)
