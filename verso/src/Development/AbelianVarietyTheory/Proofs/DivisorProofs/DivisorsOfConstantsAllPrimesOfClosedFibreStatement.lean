import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsAllPrimesOfClosedFibre
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.divisorsOfConstantsAllPrimes_of_closedFibre : GlobalTheory.VertUnits.DivConstLocal → GlobalTheory.VertUnits.DivConstAll := by
  first | exact @GlobalTheory.VertUnits.divConstAll_of_divConstLocal | exact GlobalTheory.VertUnits.divConstAll_of_divConstLocal | (intros; apply GlobalTheory.VertUnits.divConstAll_of_divConstLocal <;> assumption)
