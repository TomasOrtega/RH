import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingMirabolicCosetsStatement
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RSUnfold.unfolding_mirabolic_cosets` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnfoldingMirabolicCosetsStatement.lean&line=450#L450)
-/
theorem _root_.GlobalTheory.T.unfolding_mirabolic_cosets_statement : Ad3.R.G2b := by
  first | exact @GlobalTheory.CompanionTheory.RSUnfold.unfolding_mirabolic_cosets | exact GlobalTheory.CompanionTheory.RSUnfold.unfolding_mirabolic_cosets | (intros; apply GlobalTheory.CompanionTheory.RSUnfold.unfolding_mirabolic_cosets <;> assumption)
