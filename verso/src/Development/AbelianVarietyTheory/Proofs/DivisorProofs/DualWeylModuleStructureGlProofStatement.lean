import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylModuleStructureGlProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.dualWeylModuleStructureGl_proof : GlobalTheory.LeviCut.NablaGl := by
  first | exact @GlobalTheory.LeviCut.nablaGl | exact GlobalTheory.LeviCut.nablaGl | (intros; apply GlobalTheory.LeviCut.nablaGl <;> assumption)
