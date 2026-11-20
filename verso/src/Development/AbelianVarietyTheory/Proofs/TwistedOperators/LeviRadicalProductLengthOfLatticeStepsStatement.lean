import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviRadicalProductLengthOfLatticeSteps
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertZeta.pointwise_of_steps` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FLeviRadicalProductLengthOfLatticeSteps.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.leviRadicalProductLength_of_lattice_steps : AddVec → Dual → SpanEq → Heis → Pointwise := by
  first | exact @GlobalTheory.InertZeta.pointwise_of_steps | exact GlobalTheory.InertZeta.pointwise_of_steps | (intros; apply GlobalTheory.InertZeta.pointwise_of_steps <;> assumption)
