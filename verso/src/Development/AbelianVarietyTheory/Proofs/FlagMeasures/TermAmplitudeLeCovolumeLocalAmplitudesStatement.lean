import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAmplitudeLeCovolumeLocalAmplitudes
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.termAmplitude_le_covolume_localAmplitudes : GlobalTheory.TypeAsm.FactC := by
  first | exact @GlobalTheory.TypeAsm.factC_holds | exact GlobalTheory.TypeAsm.factC_holds | (intros; apply GlobalTheory.TypeAsm.factC_holds <;> assumption)
