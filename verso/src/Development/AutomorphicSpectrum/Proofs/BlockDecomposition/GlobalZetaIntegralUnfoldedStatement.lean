import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalZetaIntegralUnfolded
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RankinUnfold.unfolding` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGlobalZetaIntegralUnfolded.lean&line=276#L276)
-/
theorem _root_.GlobalTheory.T.global_zeta_integral_unfolded : Ad3.R.G2c → Ad3.R.G3 → Ad3.R.G3a → Ad3.R.G5 := by
  first | exact @GlobalTheory.CompanionTheory.RankinUnfold.unfolding | exact GlobalTheory.CompanionTheory.RankinUnfold.unfolding | (intros; apply GlobalTheory.CompanionTheory.RankinUnfold.unfolding <;> assumption)
