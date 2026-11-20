import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialDescentOfMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPolynomialDescentOfMap.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.polynomial_descent_of_map : PolMapSt → PolDescSt := by
  first | exact @GlobalTheory.TorRef.polDescSt_of_polMapSt | exact GlobalTheory.TorRef.polDescSt_of_polMapSt | (intros; apply GlobalTheory.TorRef.polDescSt_of_polMapSt <;> assumption)
