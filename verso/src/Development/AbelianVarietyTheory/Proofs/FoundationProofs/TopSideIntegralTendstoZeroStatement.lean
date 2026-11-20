import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TopSideIntegralTendstoZero
open MeasureTheory Filter Topology Set
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.top_side_integral_tendsto_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FTopSideIntegralTendstoZero.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.tendsto_integral_shifted_segment_zero_of_exp_decay : ∀ (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ), ContinuousOn g {z : ℂ | 0 < z.im} → 0 < c →
    (∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) → 1 ≤ τ.im →
    Tendsto (fun S : ℝ => ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I)) atTop (𝓝 0) := by
  first | exact @GlobalTheory.top_side_integral_tendsto_zero | exact GlobalTheory.top_side_integral_tendsto_zero | (intros; apply GlobalTheory.top_side_integral_tendsto_zero <;> assumption)
