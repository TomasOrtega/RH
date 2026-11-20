import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterIntegralProperties
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCentralCharacterIntegralProperties.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.central_character_integral_properties : Ad3.R.G1a → Ad3.R.G1 := by
  first | exact @GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing | exact GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing | (intros; apply GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing <;> assumption)
