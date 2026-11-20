import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsHilbertSchmidtOrthonormalApply
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitHeightSummableExpNegAbs
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_isHilbertSchmidt_orthonormal_apply` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsIsHilbertSchmidtOrthonormalApply.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_isHilbertSchmidt_orthonormal_apply_alt : ∀ (H K : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (J : Type) (u : J → H) (w : J → K), Orthonormal ℂ u → Summable (fun j => ‖w j‖ ^ 2) → ∃ G : H →L[ℂ] K, (∀ j, G (u j) = w j) ∧ (∀ v, (∀ j, inner ℂ (u j) v = 0) → G v = 0) ∧ GlobalTheory.OpTrace.IsHilbertSchmidt G := by
  first | exact @GlobalTheory.exists_isHilbertSchmidt_orthonormal_apply | exact GlobalTheory.exists_isHilbertSchmidt_orthonormal_apply | (intros; apply GlobalTheory.exists_isHilbertSchmidt_orthonormal_apply <;> assumption)
