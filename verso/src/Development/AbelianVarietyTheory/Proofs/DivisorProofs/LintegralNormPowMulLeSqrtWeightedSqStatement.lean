import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormPowMulLeSqrtWeightedSq
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.lintegral_norm_pow_mul_le_sqrt_weighted_sq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLintegralNormPowMulLeSqrtWeightedSq.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_lintegral_norm_pow_mul_le_sqrt_weighted_sq : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] [NormedAddCommGroup F], ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (H : E → F), Continuous H → ∀ k : ℕ, ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖H z‖) ∂μ ≤ C * (∫⁻ z, ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) ∂μ + ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖H z‖) ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  first | exact @GlobalTheory.lintegral_norm_pow_mul_le_sqrt_weighted_sq | exact GlobalTheory.lintegral_norm_pow_mul_le_sqrt_weighted_sq | (intros; apply GlobalTheory.lintegral_norm_pow_mul_le_sqrt_weighted_sq <;> assumption)
