import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorRef.polSuppSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPolynomialSupportHolds.lean&line=202#L202)
-/
theorem _root_.GlobalTheory.T.polynomial_support_holds : PolSuppSt := by
  first | exact @GlobalTheory.TorRef.polSuppSt | exact GlobalTheory.TorRef.polSuppSt | (intros; apply GlobalTheory.TorRef.polSuppSt <;> assumption)
