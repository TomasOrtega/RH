import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermDeterminedByFrameClassAndIsometry
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.term_determined_by_frameClass_and_isometry : GlobalTheory.TypeAsm.InjC := by
  first | exact @GlobalTheory.TypeAsm.InjProof.injC | exact GlobalTheory.TypeAsm.InjProof.injC | (intros; apply GlobalTheory.TypeAsm.InjProof.injC <;> assumption)
