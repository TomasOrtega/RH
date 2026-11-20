import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianPolynomialMultiplesDense
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GaussDense.gauss_dense` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGaussianPolynomialMultiplesDense.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.gaussian_polynomial_multiples_dense : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℂ), (∀ x, x ≠ 0 → 0 < (Q x x).re) →
    ∀ g : SchwartzMap V ℂ, (∀ x, g x = Complex.exp (-(Q x x))) →
    ∀ N : Submodule ℂ (SchwartzMap V ℂ), g ∈ N →
    (∀ f ∈ N, ∀ ℓ : V →ₗ[ℝ] ℝ, ∃ f₁ ∈ N, ∀ x, f₁ x = (ℓ x : ℂ) * f x) →
    Dense (N : Set (SchwartzMap V ℂ)) := by
  first | exact @GlobalTheory.GaussDense.gauss_dense | exact GlobalTheory.GaussDense.gauss_dense | (intros; apply GlobalTheory.GaussDense.gauss_dense <;> assumption)
