import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationGlueHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorRef.polGlueSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPolarizationGlueHolds.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.polarization_glue_holds : PolGlueSt := by
  first | exact @GlobalTheory.TorRef.polGlueSt | exact GlobalTheory.TorRef.polGlueSt | (intros; apply GlobalTheory.TorRef.polGlueSt <;> assumption)
