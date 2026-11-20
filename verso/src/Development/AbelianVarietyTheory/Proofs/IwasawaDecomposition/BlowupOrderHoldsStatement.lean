import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupOrderHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.TorRef.blowOrdSt | exact GlobalTheory.TorRef.blowOrdSt | (intros; apply GlobalTheory.TorRef.blowOrdSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.blowup_order_holds : BlowOrdSt := by
  first | exact @GlobalTheory.TorRef.blowOrdSt | exact GlobalTheory.TorRef.blowOrdSt | (intros; apply GlobalTheory.TorRef.blowOrdSt <;> assumption)
