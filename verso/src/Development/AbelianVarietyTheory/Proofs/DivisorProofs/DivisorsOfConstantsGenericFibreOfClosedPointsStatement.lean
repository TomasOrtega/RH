import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsGenericFibreOfClosedPoints
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.VertUnits.divConstGeneric_of_divConstClosedPts | exact GlobalTheory.VertUnits.divConstGeneric_of_divConstClosedPts | (intros; apply GlobalTheory.VertUnits.divConstGeneric_of_divConstClosedPts <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.divisorsOfConstants_genericFibre_of_closedPoints : GlobalTheory.VertUnits.DivConstClosedPts → GlobalTheory.VertUnits.DivConstGeneric := by
  first | exact @GlobalTheory.VertUnits.divConstGeneric_of_divConstClosedPts | exact GlobalTheory.VertUnits.divConstGeneric_of_divConstClosedPts | (intros; apply GlobalTheory.VertUnits.divConstGeneric_of_divConstClosedPts <;> assumption)
