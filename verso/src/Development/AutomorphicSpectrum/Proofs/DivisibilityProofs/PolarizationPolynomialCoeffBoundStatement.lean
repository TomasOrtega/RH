import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PolarizationPolynomialCoeffBound
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Top.polarisation_functional` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FPolarizationPolynomialCoeffBound.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.polarization_polynomial_coeff_bound : ∀ (J : Type) [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ), ∃ Pl : MvPolynomial J ℝ, Pl.IsHomogeneous d ∧ (∀ c : J → ℝ, eval c Pl = Φ ((-∑ x, C (c x) * X x) ^ d)) ∧ (∀ m : J →₀ ℕ, m.degree = d → coeff m Pl = (-1) ^ d * (m.multinomial : ℝ) * Φ (monomial m 1)) ∧ ∀ m : J →₀ ℕ, m.degree = d → |Φ (monomial m 1)| ≤ |coeff m Pl| := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.polarisation_functional | exact GlobalTheory.CompanionTheory.Ar.Top.polarisation_functional | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.polarisation_functional <;> assumption)
