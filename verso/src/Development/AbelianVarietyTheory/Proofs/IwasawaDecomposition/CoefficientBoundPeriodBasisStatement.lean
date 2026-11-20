import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientBoundPeriodBasis
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.coords_bounded_by_period_matrix` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCoefficientBoundPeriodBasis.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.coefficient_bound_period_basis : ∀ (g r : ℕ) (lam : Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ) (E F : Fin g → Fin g → ℂ) (τ : Fin g → Fin g → ℂ) (P Q : Fin r → Fin g → ℝ), (∀ m, lam m = ∑ k, (P m k : ℂ) • E k + ∑ k, (Q m k : ℂ) • F k) → (∀ j, F j = ∑ i, τ i j • E i) → (∀ i, ∑ m, ρ i m • lam m = Pi.single i 1) → ∀ u : Fin g → ℂ, ∃ a : Fin g → ℂ, u = ∑ k, a k • E k ∧ ‖a‖ ≤ (g : ℝ) * ((r : ℝ) * ‖ρ‖ * (‖P‖ + (g : ℝ) * ‖Q‖ * ‖τ‖)) * ‖u‖ := by
  first | exact @GlobalTheory.coords_bounded_by_period_matrix | exact GlobalTheory.coords_bounded_by_period_matrix | (intros; apply GlobalTheory.coords_bounded_by_period_matrix <;> assumption)
