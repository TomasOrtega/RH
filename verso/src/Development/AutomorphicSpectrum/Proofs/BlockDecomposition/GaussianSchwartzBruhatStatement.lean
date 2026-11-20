import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianSchwartzBruhat
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGaussianSchwartzBruhat.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.gaussian_schwartz_bruhat : Ad3.R.GS := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.gaussian_exists | exact GlobalTheory.CompanionTheory.RankinSelberg.gaussian_exists | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.gaussian_exists <;> assumption)
