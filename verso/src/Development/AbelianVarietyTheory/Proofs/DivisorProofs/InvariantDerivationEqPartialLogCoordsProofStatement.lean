import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationEqPartialLogCoordsProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.InvDer.invDer | exact GlobalTheory.InvDer.invDer | (intros; apply GlobalTheory.InvDer.invDer <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.invariantDerivationEqPartialLogCoords_proof : InvDerSt := by
  first | exact @GlobalTheory.InvDer.invDer | exact GlobalTheory.InvDer.invDer | (intros; apply GlobalTheory.InvDer.invDer <;> assumption)
