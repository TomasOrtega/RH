import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupExistsHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FBlowupExistsHolds.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.blowup_exists_holds : BlowExSt := by
  first | exact @GlobalTheory.TorRef.blowExSt | exact GlobalTheory.TorRef.blowExSt | (intros; apply GlobalTheory.TorRef.blowExSt <;> assumption)
