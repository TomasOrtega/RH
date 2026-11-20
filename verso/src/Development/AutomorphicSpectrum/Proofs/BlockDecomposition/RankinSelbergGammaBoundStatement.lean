import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergGammaBound
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRankinSelbergGammaBound.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.rankin_selberg_gamma_bound : Ad3.R.RealPlaceGammaFactors := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.RealGamma.main | exact GlobalTheory.CompanionTheory.RankinSelberg.RealGamma.main | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.RealGamma.main <;> assumption)
