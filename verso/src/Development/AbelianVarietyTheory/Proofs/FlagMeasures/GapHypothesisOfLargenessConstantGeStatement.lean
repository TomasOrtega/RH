import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapHypothesisOfLargenessConstantGe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.gapC_holds : GlobalTheory.TypeAsm.GapC := by
  first | exact @GlobalTheory.TypeAsm.gapC | exact GlobalTheory.TypeAsm.gapC | (intros; apply GlobalTheory.TypeAsm.gapC <;> assumption)
