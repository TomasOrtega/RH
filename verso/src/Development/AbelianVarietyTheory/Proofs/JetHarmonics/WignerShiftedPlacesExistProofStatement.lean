import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerShiftedPlacesExistProof
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ShiftExists
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists | exact GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists | (intros; apply GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.wignerShiftedPlacesExist_proof : GlobalTheory.WigSh.ShiftExists := by
  first | exact @GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists | exact GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists | (intros; apply GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists <;> assumption)
