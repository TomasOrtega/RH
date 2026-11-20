import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianSchwartzBruhat
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RankinSelberg.gaussian_exists | exact GlobalTheory.CompanionTheory.RankinSelberg.gaussian_exists | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.gaussian_exists <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.gaussian_schwartz_bruhat : Ad3.R.GS := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.gaussian_exists | exact GlobalTheory.CompanionTheory.RankinSelberg.gaussian_exists | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.gaussian_exists <;> assumption)
