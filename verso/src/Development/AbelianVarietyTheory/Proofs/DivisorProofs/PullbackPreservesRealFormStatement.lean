import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesRealForm
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CxForm.RealPull.isReal_pull` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPullbackPreservesRealForm.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.pullback_preserves_real_form : ∀ (n m : ℕ) (L : V n →L[ℂ] V m) (α : Alt m), IsReal α → IsReal (pull L α) := by
  first | exact @GlobalTheory.CxForm.RealPull.isReal_pull | exact GlobalTheory.CxForm.RealPull.isReal_pull | (intros; apply GlobalTheory.CxForm.RealPull.isReal_pull <;> assumption)
