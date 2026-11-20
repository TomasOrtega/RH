import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorOrderHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPhiDivisorOrderHolds.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.phi_divisor_order_holds : PhiDivOSt := by
  first | exact @GlobalTheory.TorRef.phiDivO | exact GlobalTheory.TorRef.phiDivO | (intros; apply GlobalTheory.TorRef.phiDivO <;> assumption)
