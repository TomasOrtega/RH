import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterFiniteOrderDefiniteForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.levelCharacter_finiteOrder_definite_forms : GlobalTheory.BaseCmp.LevLamRoot := by
  first | exact @GlobalTheory.BaseCmp.levLamRoot | exact GlobalTheory.BaseCmp.levLamRoot | (intros; apply GlobalTheory.BaseCmp.levLamRoot <;> assumption)
