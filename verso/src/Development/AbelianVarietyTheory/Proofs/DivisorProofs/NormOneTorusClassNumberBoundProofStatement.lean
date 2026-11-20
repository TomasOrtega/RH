import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneTorusClassNumberBoundProof
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.normOneTorusClassNumberBound_proof : GlobalTheory.UCls.TorusBound := by
  first | exact @GlobalTheory.UCls.torusBound | exact GlobalTheory.UCls.torusBound | (intros; apply GlobalTheory.UCls.torusBound <;> assumption)
