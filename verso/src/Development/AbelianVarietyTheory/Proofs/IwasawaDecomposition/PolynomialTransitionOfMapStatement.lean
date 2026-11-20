import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialTransitionOfMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPolynomialTransitionOfMap.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.polynomial_transition_of_map : PolMapSt → PolTransSt := by
  first | exact @GlobalTheory.TorRef.polTransSt_of_polMapSt | exact GlobalTheory.TorRef.polTransSt_of_polMapSt | (intros; apply GlobalTheory.TorRef.polTransSt_of_polMapSt <;> assumption)
