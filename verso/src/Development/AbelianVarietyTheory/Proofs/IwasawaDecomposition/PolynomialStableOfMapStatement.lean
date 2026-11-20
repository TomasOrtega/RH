import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialStableOfMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.TorRef.polStable_of_polMap | exact GlobalTheory.TorRef.polStable_of_polMap | (intros; apply GlobalTheory.TorRef.polStable_of_polMap <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.polynomial_stable_of_map : PolMapSt → PolStableSt := by
  first | exact @GlobalTheory.TorRef.polStable_of_polMap | exact GlobalTheory.TorRef.polStable_of_polMap | (intros; apply GlobalTheory.TorRef.polStable_of_polMap <;> assumption)
