import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureEqOfLintegralSmoothEq
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.measure_eq_of_lintegral_smooth_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMeasureEqOfLintegralSmoothEq.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.measure_eq_of_lintegral_smooth_eq' : ∀ (N : ℕ) (m₁ m₂ : Measure (Fin N → ℝ)) [IsFiniteMeasureOnCompacts m₂], (∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) → ∫⁻ x, ENNReal.ofReal (φ x) ∂m₁ = ∫⁻ x, ENNReal.ofReal (φ x) ∂m₂) → m₁ = m₂ := by
  first | exact @GlobalTheory.measure_eq_of_lintegral_smooth_eq | exact GlobalTheory.measure_eq_of_lintegral_smooth_eq | (intros; apply GlobalTheory.measure_eq_of_lintegral_smooth_eq <;> assumption)
