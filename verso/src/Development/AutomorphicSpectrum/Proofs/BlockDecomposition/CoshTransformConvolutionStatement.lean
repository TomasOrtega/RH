import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoshTransformConvolution
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WaveMult.CoshMul.coshT_mul_coshT` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCoshTransformConvolution.lean&line=94#L94)
-/
theorem _root_.GlobalTheory.T.cosh_transform_convolution : ∀ (g g' : ℝ → ℝ) (T T' : ℝ) (c : ℂ), IsBump g T → IsBump g' T' → coshT g c * coshT g' c = coshT (gconv g g') c := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.CoshMul.coshT_mul_coshT | exact GlobalTheory.CompanionTheory.WaveMult.CoshMul.coshT_mul_coshT | (intros; apply GlobalTheory.CompanionTheory.WaveMult.CoshMul.coshT_mul_coshT <;> assumption)
