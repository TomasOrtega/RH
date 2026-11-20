import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMapHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorRef.polMapSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPolynomialMapHolds.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.polynomial_map_holds : PolMapSt := by
  first | exact @GlobalTheory.TorRef.polMapSt | exact GlobalTheory.TorRef.polMapSt | (intros; apply GlobalTheory.TorRef.polMapSt <;> assumption)
