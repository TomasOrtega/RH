import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylWeightSpreadBoundProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.dualWeylWeightSpreadBound_proof : GlobalTheory.LeviCut.NablaBdd := by
  first | exact @GlobalTheory.LeviCut.nablaBdd | exact GlobalTheory.LeviCut.nablaBdd | (intros; apply GlobalTheory.LeviCut.nablaBdd <;> assumption)
