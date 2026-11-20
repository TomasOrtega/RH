import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHasSumEqIntegralIndicatorHasSum
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.integral_hasSum_eq_integral_indicator_hasSum` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralHasSumEqIntegralIndicatorHasSum.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.integral_hasSum_eq_integral_indicator_hasSum' : ∀ {X ι : Type} [MeasurableSpace X] [Countable ι] (μ : Measure X) (k : ι → X → ℂ), (∀ i, Integrable (k i) μ) → {i | ∫ x, ‖k i x‖ ∂μ ≠ 0}.Finite → ∀ (p : Set ι) (K Kp : X → ℂ), (∀ x, HasSum (fun i => k i x) (K x)) → (∀ x, HasSum (fun i => p.indicator (fun i => k i x) i) (Kp x)) → (∀ i ∉ p, ∫ x, k i x ∂μ = 0) → ∫ x, K x ∂μ = ∫ x, Kp x ∂μ := by
  first | exact @GlobalTheory.integral_hasSum_eq_integral_indicator_hasSum | exact GlobalTheory.integral_hasSum_eq_integral_indicator_hasSum | (intros; apply GlobalTheory.integral_hasSum_eq_integral_indicator_hasSum <;> assumption)
