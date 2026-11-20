import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstCoeffOperatorLinearSubstitutionProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.IsoTriv.linSt_holds | exact GlobalTheory.IsoTriv.linSt_holds | (intros; apply GlobalTheory.IsoTriv.linSt_holds <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.constCoeffOperatorLinearSubstitution_proof : LinSt := by
  first | exact @GlobalTheory.IsoTriv.linSt_holds | exact GlobalTheory.IsoTriv.linSt_holds | (intros; apply GlobalTheory.IsoTriv.linSt_holds <;> assumption)
