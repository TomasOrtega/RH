import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorValueHighestWeightVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.LeviCut.StepScalarProof.stepScalar | exact GlobalTheory.LeviCut.StepScalarProof.stepScalar | (intros; apply GlobalTheory.LeviCut.StepScalarProof.stepScalar <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.projector_value_highest_weight_vector : GlobalTheory.LeviCut.StepScalar := by
  first | exact @GlobalTheory.LeviCut.StepScalarProof.stepScalar | exact GlobalTheory.LeviCut.StepScalarProof.stepScalar | (intros; apply GlobalTheory.LeviCut.StepScalarProof.stepScalar <;> assumption)
