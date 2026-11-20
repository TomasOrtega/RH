import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupPolarizationHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorRef.blowPolSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FBlowupPolarizationHolds.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.blowup_polarization_holds : BlowPolSt := by
  first | exact @GlobalTheory.TorRef.blowPolSt | exact GlobalTheory.TorRef.blowPolSt | (intros; apply GlobalTheory.TorRef.blowPolSt <;> assumption)
