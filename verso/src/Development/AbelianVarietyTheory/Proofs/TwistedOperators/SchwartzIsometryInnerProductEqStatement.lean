import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzIsometryInnerProductEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.schwartz_L2_isometry_preserves_inner` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSchwartzIsometryInnerProductEq.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.schwartz_isometry_inner_product_eq : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ),
    (∀ f, ∫ x, ‖T f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ f g : SchwartzMap V ℂ, ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ = ∫ x, f x * starRingEnd ℂ (g x) ∂μ := by
  first | exact @GlobalTheory.schwartz_L2_isometry_preserves_inner | exact GlobalTheory.schwartz_L2_isometry_preserves_inner | (intros; apply GlobalTheory.schwartz_L2_isometry_preserves_inner <;> assumption)
