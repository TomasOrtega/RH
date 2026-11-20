import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RefinementHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FRefinementHolds.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.refinement_holds : RefineSt := by
  first | exact @GlobalTheory.TorRef.refineSt | exact GlobalTheory.TorRef.refineSt | (intros; apply GlobalTheory.TorRef.refineSt <;> assumption)
