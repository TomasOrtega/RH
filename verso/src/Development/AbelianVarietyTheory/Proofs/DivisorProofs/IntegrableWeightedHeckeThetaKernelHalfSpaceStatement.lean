import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableWeightedHeckeThetaKernelHalfSpace
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegrableWeightedHeckeThetaKernelHalfSpace.lean&line=169#L169)
-/
theorem _root_.GlobalTheory.T.integrable_weighted_heckeThetaKernel_halfSpace : ∀ (I : Type) [Fintype I] {ι : Type} (e : ι → I → ℂ) (a : ι → ℂ) (n : I → ℤ) (q : (I → ℝ) → ℝ) (B R : ℝ), (∃ i, n i ≠ 0) → (∀ ε : ℝ, 0 < ε → Summable (fun j => ‖a j‖ * Real.exp (-ε * ‖e j‖ ^ 2))) → (∃ δ : ℝ, 0 < δ ∧ ∀ j, a j ≠ 0 → e j ≠ 0 → δ ≤ ‖e j‖) → Measurable q → (∀ y, |q y| ≤ B) → (∀ y, q y ≠ 0 → ∀ i j, y i - y j ≤ R) → MeasureTheory.AEStronglyMeasurable (fun y => (q y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y) MeasureTheory.volume ∧ ∀ σ : ℝ, MeasureTheory.Integrable (fun y => ‖(q y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y‖ * Real.exp (σ * ∑ i, y i)) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) := by
  first | exact @GlobalTheory.HeckeTheta.Decay.integrable_weight_theta | exact GlobalTheory.HeckeTheta.Decay.integrable_weight_theta | (intros; apply GlobalTheory.HeckeTheta.Decay.integrable_weight_theta <;> assumption)
