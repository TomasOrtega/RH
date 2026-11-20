import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothVanishingHyperplaneFactor
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Chamber.hadamard_div_linear | exact GlobalTheory.Chamber.hadamard_div_linear | (intros; apply GlobalTheory.Chamber.hadamard_div_linear <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.smooth_vanishing_hyperplane_factor : ∀ {k : ℕ} (b : A0 k) (N : A0 k → ℂ), b ≠ 0 → ContDiff ℝ ∞ N → (∀ x, ⟪x, b⟫_ℝ = 0 → N x = 0) →
  ∃ F : A0 k → ℂ, ContDiff ℝ ∞ F ∧ ∀ x, N x = (⟪x, b⟫_ℝ : ℂ) * F x := by
  first | exact @GlobalTheory.Chamber.hadamard_div_linear | exact GlobalTheory.Chamber.hadamard_div_linear | (intros; apply GlobalTheory.Chamber.hadamard_div_linear <;> assumption)
