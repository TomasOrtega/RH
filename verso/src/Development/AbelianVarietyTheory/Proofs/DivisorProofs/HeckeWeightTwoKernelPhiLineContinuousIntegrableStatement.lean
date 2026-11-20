import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoKernelPhiLineContinuousIntegrable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex MeasureTheory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeckeWeightTwoKernelPhiLineContinuousIntegrable.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.heckeWeightTwoKernelPhi_line_continuous_integrable : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧ MeasureTheory.Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := by
  first | exact @GlobalTheory.HeckeTwo.phi_line_continuous_integrable | exact GlobalTheory.HeckeTwo.phi_line_continuous_integrable | (intros; apply GlobalTheory.HeckeTwo.phi_line_continuous_integrable <;> assumption)
