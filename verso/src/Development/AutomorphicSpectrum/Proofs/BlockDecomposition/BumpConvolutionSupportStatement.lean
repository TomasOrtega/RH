import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpConvolutionSupport
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FBumpConvolutionSupport.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.bump_convolution_support : ∀ (g g' : ℝ → ℝ) (T T' : ℝ), IsBump g T → IsBump g' T' → IsBump (gconv g g') (T + T') := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.isBump_gconv | exact GlobalTheory.CompanionTheory.WaveMult.isBump_gconv | (intros; apply GlobalTheory.CompanionTheory.WaveMult.isBump_gconv <;> assumption)
