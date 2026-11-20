import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexHessianLogFubiniStudy
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FComplexHessianLogFubiniStudy.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.complex_hessian_log_fubini_study : ∀ (d : ℕ) (β : Type) [Fintype β] (U : Set (V d)) (f : β → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (f j) U) → ∀ z ∈ U, cHess d (fun v => ((Real.log (1 + ∑ j, ‖f j v‖ ^ 2) : ℝ) : ℂ)) z = fsLevi (fun j => f j z) (Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1)) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.cHess_log_one_add_sum | exact GlobalTheory.CompanionTheory.FSCrofton.cHess_log_one_add_sum | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.cHess_log_one_add_sum <;> assumption)
