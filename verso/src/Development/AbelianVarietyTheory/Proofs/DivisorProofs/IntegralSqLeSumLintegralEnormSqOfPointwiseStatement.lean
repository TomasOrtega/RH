import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSqLeSumLintegralEnormSqOfPointwise
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralSqLeSumLintegralEnormSqOfPointwise.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.integral_sq_le_sum_lintegral_enorm_sq_of_pointwise : ∀ (E : Type) [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] (μ : MeasureTheory.Measure E)
    (ι : Type) [Fintype ι] (f : E → ℝ) (g : ι → E → ℂ) (C : ℝ), (∀ a, Continuous (g a)) →
    (∀ x, f x ^ 2 ≤ C * ∑ a, ‖g a x‖ ^ 2) →
    ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) ≤ ENNReal.ofReal C * ∑ a, ∫⁻ x, ‖g a x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.sq_le_sum_enorm_sq_lintegral_bound | exact GlobalTheory.sq_le_sum_enorm_sq_lintegral_bound | (intros; apply GlobalTheory.sq_le_sum_enorm_sq_lintegral_bound <;> assumption)
