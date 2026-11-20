import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulatedSchwartzSeminormPolynomial
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FModulatedSchwartzSeminormPolynomial.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.modulated_schwartz_seminorm_polynomial : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V) (h : SchwartzMap V ℂ) (v : V → SchwartzMap V ℂ),
    (∀ μ x, v μ x = Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ)) * h x) →
    ∀ k n : ℕ, ∃ C : ℝ, ∀ μ, SchwartzMap.seminorm ℂ k n (v μ) ≤ C * (1 + ‖μ‖) ^ n := by
  first | exact @GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth | exact GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth | (intros; apply GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth <;> assumption)
