import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialGrowthOfPeriodicIntegralSpans
import Mathlib
open Filter Topology

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StripGrowth.strip_growth` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPolynomialGrowthOfPeriodicIntegralSpans.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.polynomial_growth_of_periodic_integral_spans : ∀ (g m : ℕ) (lam : ℂ → Fin m → Fin g → ℂ) (C : ℝ) (k : ℕ), ContinuousOn lam {s : ℂ | s.re < 0} → (∀ s : ℂ, s.re < 0 → LinearIndependent ℝ (lam s)) → (∀ s : ℂ, s.re < 0 → ∀ z : Fin g → ℂ, (∃ n : Fin m → ℤ, z = ∑ j, n j • lam (s + 2 * Real.pi * Complex.I) j) ↔ ∃ n : Fin m → ℤ, z = ∑ j, n j • lam s j) → (∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ Real.pi → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k) → ∀ R : ℝ, ∃ C' : ℝ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ R → ‖lam s‖ ≤ C' * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.StripGrowth.strip_growth | exact GlobalTheory.StripGrowth.strip_growth | (intros; apply GlobalTheory.StripGrowth.strip_growth <;> assumption)
