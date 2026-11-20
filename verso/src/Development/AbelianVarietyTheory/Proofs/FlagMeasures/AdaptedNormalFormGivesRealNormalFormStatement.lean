import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormGivesRealNormalForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.adaptedNormalForm_gives_real_normal_form : GlobalTheory.TypeAsm.FrameC := by
  first | exact @GlobalTheory.TypeAsm.frameC_holds | exact GlobalTheory.TypeAsm.frameC_holds | (intros; apply GlobalTheory.TypeAsm.frameC_holds <;> assumption)
