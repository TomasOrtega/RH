import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupOrderHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FBlowupOrderHolds.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.blowup_order_holds : BlowOrdSt := by
  first | exact @GlobalTheory.TorRef.blowOrdSt | exact GlobalTheory.TorRef.blowOrdSt | (intros; apply GlobalTheory.TorRef.blowOrdSt <;> assumption)
