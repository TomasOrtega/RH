import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianHarmonicProductKernelContinuousBounded
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbAApply
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeTheta.GaussBound.gauss_cont_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGaussianHarmonicProductKernelContinuousBounded.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.gaussianHarmonicProductKernel_continuous_bounded : ∀ (I : Type) [Fintype I] (n : I → ℤ), Continuous (fun w : EuclideanSpace ℂ I => GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)) ∧ ∃ C : ℝ, ∀ w : EuclideanSpace ℂ I, ‖GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)‖ ≤ C * Real.exp (-Real.pi * ‖w‖ ^ 2) := by
  first | exact @GlobalTheory.HeckeTheta.GaussBound.gauss_cont_bound | exact GlobalTheory.HeckeTheta.GaussBound.gauss_cont_bound | (intros; apply GlobalTheory.HeckeTheta.GaussBound.gauss_cont_bound <;> assumption)
