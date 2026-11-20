import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonicFactorCoefficientsIntegral

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMonicFactorCoefficientsIntegral.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.monic_factor_coefficients_integral : ∀ (A : Type) [CommRing A] [Algebra ℂ A] (P Q : Polynomial A) (c₁ c₂ : ℂ), P.Monic → Q.Monic → (∀ u : ℂ, IsIntegral ℂ (P.eval (algebraMap ℂ A (u + c₁)) * Q.eval (algebraMap ℂ A (u + c₂)))) → ∀ k, IsIntegral ℂ (P.coeff k) ∧ IsIntegral ℂ (Q.coeff k) := by
  first | exact @GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product | exact GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product | (intros; apply GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product <;> assumption)
