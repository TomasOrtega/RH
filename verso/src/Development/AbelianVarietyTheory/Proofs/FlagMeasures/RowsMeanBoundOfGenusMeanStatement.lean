import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsMeanBoundOfGenusMean
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.TypeAsm.rowsMean | exact GlobalTheory.TypeAsm.rowsMean | (intros; apply GlobalTheory.TypeAsm.rowsMean <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.rowsMeanC_holds : GlobalTheory.TypeAsm.RowsMeanC := by
  first | exact @GlobalTheory.TypeAsm.rowsMean | exact GlobalTheory.TypeAsm.rowsMean | (intros; apply GlobalTheory.TypeAsm.rowsMean <;> assumption)
