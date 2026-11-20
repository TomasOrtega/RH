import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLeviProjectionDenominatorsOfHypotheses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.dualWeylLeviProjectionDenominators_of_hypotheses : GlobalTheory.LeviCut.ResLat → GlobalTheory.LeviCut.ResHw → GlobalTheory.LeviCut.ResDer → GlobalTheory.LeviCut.LeviProj := by
  first | exact @GlobalTheory.LeviCut.leviProj_of | exact GlobalTheory.LeviCut.leviProj_of | (intros; apply GlobalTheory.LeviCut.leviProj_of <;> assumption)
