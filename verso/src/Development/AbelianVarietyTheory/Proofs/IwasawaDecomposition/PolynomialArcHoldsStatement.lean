import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialArcHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PolArc.polArc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPolynomialArcHolds.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.polynomial_arc_holds : PolArcSt := by
  first | exact @GlobalTheory.PolArc.polArc | exact GlobalTheory.PolArc.polArc | (intros; apply GlobalTheory.PolArc.polArc <;> assumption)
