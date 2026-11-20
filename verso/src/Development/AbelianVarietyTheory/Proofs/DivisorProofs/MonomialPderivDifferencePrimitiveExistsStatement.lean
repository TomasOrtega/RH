import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialPderivDifferencePrimitiveExists
import Mathlib
open MvPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMonomialPderivDifferencePrimitiveExists.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.monomial_pderiv_difference_primitive_exists : ∀ (n : ℕ) (i i' : Fin (n + 1)), i ≠ i' → ∀ (α : Fin (n + 1) →₀ ℕ) (c : ℝ), ∃ J₁ R : MvPolynomial (Fin (n + 1)) ℝ, pderiv i' J₁ - pderiv i J₁ = monomial α c ∧ J₁ = (-(1 / ((α i : ℝ) + 1))) • (X i * monomial α c) + R ∧ ∀ β ∈ R.support, β i' < α i' ∧ ∀ j, j ≠ i → j ≠ i' → β j = α j := by
  first | exact @GlobalTheory.monomial_pderiv_diff_primitive | exact GlobalTheory.monomial_pderiv_diff_primitive | (intros; apply GlobalTheory.monomial_pderiv_diff_primitive <;> assumption)
