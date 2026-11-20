import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedOfSmoothOverField
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isReduced_of_smooth_over_field` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsReducedOfSmoothOverField.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.isReduced_of_smooth_over_field' : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Algebra.Smooth K A], IsReduced A := by
  first | exact @GlobalTheory.isReduced_of_smooth_over_field | exact GlobalTheory.isReduced_of_smooth_over_field | (intros; apply GlobalTheory.isReduced_of_smooth_over_field <;> assumption)
