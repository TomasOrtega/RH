import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialStableOfMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorRef.polStable_of_polMap` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPolynomialStableOfMap.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.polynomial_stable_of_map : PolMapSt → PolStableSt := by
  first | exact @GlobalTheory.TorRef.polStable_of_polMap | exact GlobalTheory.TorRef.polStable_of_polMap | (intros; apply GlobalTheory.TorRef.polStable_of_polMap <;> assumption)
