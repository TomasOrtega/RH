import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFormSumOfSquares
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.two_mul_functional_eq_sum_diag` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FSymmetricFormSumOfSquares.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.symmetric_form_sum_of_squares : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), ∃ (m : ℕ) (y : Fin m → X) (a : Fin m → ℤ), ∀ β : LinearMap.BilinForm ℤ X, (∀ u v, β u v = β v u) → 2 * ℓ β = ∑ i, a i * β (y i) (y i) := by
  first | exact @GlobalTheory.two_mul_functional_eq_sum_diag | exact GlobalTheory.two_mul_functional_eq_sum_diag | (intros; apply GlobalTheory.two_mul_functional_eq_sum_diag <;> assumption)
