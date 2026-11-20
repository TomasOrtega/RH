import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationGlueHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.TorRef.polGlueSt | exact GlobalTheory.TorRef.polGlueSt | (intros; apply GlobalTheory.TorRef.polGlueSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.polarization_glue_holds : PolGlueSt := by
  first | exact @GlobalTheory.TorRef.polGlueSt | exact GlobalTheory.TorRef.polGlueSt | (intros; apply GlobalTheory.TorRef.polGlueSt <;> assumption)
