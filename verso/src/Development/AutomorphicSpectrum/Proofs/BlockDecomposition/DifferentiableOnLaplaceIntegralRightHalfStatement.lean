import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnLaplaceIntegralRightHalf
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDifferentiableOnLaplaceIntegralRightHalf.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.differentiableOn_laplace_integral_right_half : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (G : X → ℂ) (L : X → ℝ), AEStronglyMeasurable G μ → Measurable L → (∀ σ : ℝ, 0 < σ → Integrable (fun x => ‖G x‖ * Real.exp (σ * L x)) μ) → DifferentiableOn ℂ (fun u : ℂ => ∫ x, G x * Complex.exp (u * (L x : ℂ)) ∂μ) {u : ℂ | 0 < u.re} := by
  first | exact @GlobalTheory.CompanionTheory.HoloFamily.differentiableOn_integral_mul_cexp | exact GlobalTheory.CompanionTheory.HoloFamily.differentiableOn_integral_mul_cexp | (intros; apply GlobalTheory.CompanionTheory.HoloFamily.differentiableOn_integral_mul_cexp <;> assumption)
