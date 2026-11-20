import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledLatticePrimitiveIsotropicFrameCompletion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FDoubledLatticePrimitiveIsotropicFrameCompletion.lean&line=194#L194)
-/
theorem _root_.GlobalTheory.T.doubledLattice_primitive_isotropic_frame_completion : Completion := by
  first | exact @GlobalTheory.FrameCompletion.completion | exact GlobalTheory.FrameCompletion.completion | (intros; apply GlobalTheory.FrameCompletion.completion <;> assumption)
