import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerShiftedPlacesExistProof
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ShiftExists
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FWignerShiftedPlacesExistProof.lean&line=129#L129)
-/
theorem _root_.GlobalTheory.T.wignerShiftedPlacesExist_proof : GlobalTheory.WigSh.ShiftExists := by
  first | exact @GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists | exact GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists | (intros; apply GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists <;> assumption)
