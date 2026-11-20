import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProof
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.equivFramesSameSecondLatticeFiber_proof : GlobalTheory.TypeAsm.FibC := by
  first | exact @GlobalTheory.TypeAsm.FibProof.fibC | exact GlobalTheory.TypeAsm.FibProof.fibC | (intros; apply GlobalTheory.TypeAsm.FibProof.fibC <;> assumption)
