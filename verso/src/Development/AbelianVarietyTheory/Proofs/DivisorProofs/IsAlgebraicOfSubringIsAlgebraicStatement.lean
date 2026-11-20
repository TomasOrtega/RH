import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfSubringIsAlgebraic
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isAlgebraic_of_subring_isAlgebraic` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsAlgebraicOfSubringIsAlgebraic.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.isAlgebraic_of_isAlgebraic_over_algebraic_subring : ∀ {L : Type} [Field L] [Algebra ℂ L] (S : Subalgebra ℂ L) (B : Subring L) (z : L),
  (∀ b ∈ B, IsAlgebraic S b) → IsAlgebraic B z → IsAlgebraic S z := by
  first | exact @GlobalTheory.isAlgebraic_of_subring_isAlgebraic | exact GlobalTheory.isAlgebraic_of_subring_isAlgebraic | (intros; apply GlobalTheory.isAlgebraic_of_subring_isAlgebraic <;> assumption)
