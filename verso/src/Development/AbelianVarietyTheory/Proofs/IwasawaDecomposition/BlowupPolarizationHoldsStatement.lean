import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupPolarizationHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.TorRef.blowPolSt | exact GlobalTheory.TorRef.blowPolSt | (intros; apply GlobalTheory.TorRef.blowPolSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.blowup_polarization_holds : BlowPolSt := by
  first | exact @GlobalTheory.TorRef.blowPolSt | exact GlobalTheory.TorRef.blowPolSt | (intros; apply GlobalTheory.TorRef.blowPolSt <;> assumption)
