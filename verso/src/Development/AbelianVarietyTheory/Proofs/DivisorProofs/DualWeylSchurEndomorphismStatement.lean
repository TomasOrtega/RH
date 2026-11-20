import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylSchurEndomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.LeviCut.nablaSchur | exact GlobalTheory.LeviCut.nablaSchur | (intros; apply GlobalTheory.LeviCut.nablaSchur <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.dualWeyl_schur_endomorphism : GlobalTheory.LeviCut.NablaSchur := by
  first | exact @GlobalTheory.LeviCut.nablaSchur | exact GlobalTheory.LeviCut.nablaSchur | (intros; apply GlobalTheory.LeviCut.nablaSchur <;> assumption)
