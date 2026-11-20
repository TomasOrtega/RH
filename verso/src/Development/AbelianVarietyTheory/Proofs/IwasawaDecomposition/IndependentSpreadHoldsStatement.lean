import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndependentSpreadHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.TorRef.indepSpreadSt | exact GlobalTheory.TorRef.indepSpreadSt | (intros; apply GlobalTheory.TorRef.indepSpreadSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.independent_spread_holds : IndepSpreadSt := by
  first | exact @GlobalTheory.TorRef.indepSpreadSt | exact GlobalTheory.TorRef.indepSpreadSt | (intros; apply GlobalTheory.TorRef.indepSpreadSt <;> assumption)
