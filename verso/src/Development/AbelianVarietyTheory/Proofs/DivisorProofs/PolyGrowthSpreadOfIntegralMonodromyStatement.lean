import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyGrowthSpreadOfIntegralMonodromy
import Mathlib
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.polyGrowth_spread_of_integral_monodromy` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPolyGrowthSpreadOfIntegralMonodromy.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.polyGrowth_strip_of_integral_monodromy : ∀ (g m : ℕ) (lam : ℂ → Fin m → Fin g → ℂ) (C : ℝ) (k : ℕ) (P Q : Fin m → Fin m → ℤ), (∀ s : ℂ, s.re < 0 → ∀ j, lam (s + 2 * Real.pi * Complex.I) j = ∑ i, P j i • lam s i) → (∀ s : ℂ, s.re < 0 → ∀ j, lam s j = ∑ i, Q j i • lam (s + 2 * Real.pi * Complex.I) i) → (∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ Real.pi → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k) → ∀ R : ℝ, ∃ C' : ℝ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ R → ‖lam s‖ ≤ C' * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.polyGrowth_spread_of_integral_monodromy | exact GlobalTheory.polyGrowth_spread_of_integral_monodromy | (intros; apply GlobalTheory.polyGrowth_spread_of_integral_monodromy <;> assumption)
