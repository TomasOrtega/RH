import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralAbsoluteConvergence
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FZetaIntegralAbsoluteConvergence.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.zeta_integral_absolute_convergence : Ad3.R.AdelicThetaPoissonSummation := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.theta_functional_equation | exact GlobalTheory.CompanionTheory.RankinSelberg.theta_functional_equation | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.theta_functional_equation <;> assumption)
