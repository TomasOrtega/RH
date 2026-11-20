import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightDifferentiableLogarithmic
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Qf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorExplicitFormula
open Ad3.LR Ad3.LR.DTr GlobalTheory.CompanionTheory.DInt2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWeightDifferentiableLogarithmic.lean&line=123#L123)
-/
theorem _root_.GlobalTheory.T.weight_differentiable_logarithmic : ∀ k : ℕ, 3 ≤ k → ∀ h : M22, 0 < (Matrix.of h).det → DifferentiableAt ℝ (w0 k) h ∧ ∀ X : M22, fderiv ℝ (w0 k) h X = w0 k h * ell k h X := by
  first | exact @GlobalTheory.CompanionTheory.DInt2.dw0 | exact GlobalTheory.CompanionTheory.DInt2.dw0 | (intros; apply GlobalTheory.CompanionTheory.DInt2.dw0 <;> assumption)
