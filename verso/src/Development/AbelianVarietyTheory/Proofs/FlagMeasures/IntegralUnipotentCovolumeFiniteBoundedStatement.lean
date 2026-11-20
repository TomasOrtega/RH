import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCovolumeFiniteBounded
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.integralUnipotent_covolume_finite_bounded : GlobalTheory.TypeAsm.CovNC := by
  first | exact @GlobalTheory.TypeAsm.covNC_holds | exact GlobalTheory.TypeAsm.covNC_holds | (intros; apply GlobalTheory.TypeAsm.covNC_holds <;> assumption)
