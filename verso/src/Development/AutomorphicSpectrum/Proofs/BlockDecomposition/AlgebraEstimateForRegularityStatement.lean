import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraEstimateForRegularity
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SkewWords.algEst` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAlgebraEstimateForRegularity.lean&line=266#L266)
-/
theorem _root_.GlobalTheory.T.algebra_estimate_for_regularity : PositivityTheory.RgBcC.AlgEst := by
  first | exact @GlobalTheory.CompanionTheory.SkewWords.algEst | exact GlobalTheory.CompanionTheory.SkewWords.algEst | (intros; apply GlobalTheory.CompanionTheory.SkewWords.algEst <;> assumption)
