import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergGammaFactor
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRankinSelbergGammaFactor.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.rankin_selberg_gamma_factor : Ad3.R.LocalGammaFunctionalEquation := by
  first | exact @GlobalTheory.CompanionTheory.TateGamma.gam_strip | exact GlobalTheory.CompanionTheory.TateGamma.gam_strip | (intros; apply GlobalTheory.CompanionTheory.TateGamma.gam_strip <;> assumption)
