import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndependentSpreadHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIndependentSpreadHolds.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.independent_spread_holds : IndepSpreadSt := by
  first | exact @GlobalTheory.TorRef.indepSpreadSt | exact GlobalTheory.TorRef.indepSpreadSt | (intros; apply GlobalTheory.TorRef.indepSpreadSt <;> assumption)
