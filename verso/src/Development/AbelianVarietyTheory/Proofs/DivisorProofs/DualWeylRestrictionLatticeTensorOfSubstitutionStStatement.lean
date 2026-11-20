import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylRestrictionLatticeTensorOfSubstitutionSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.dualWeylRestrictionLatticeTensor_of_substitutionStable : GlobalTheory.LeviCut.SubstMem → GlobalTheory.LeviCut.ResLat := by
  first | exact @GlobalTheory.LeviCut.resLat_of_substMem | exact GlobalTheory.LeviCut.resLat_of_substMem | (intros; apply GlobalTheory.LeviCut.resLat_of_substMem <;> assumption)
