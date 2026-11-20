import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainDescription
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFundamentalDomainDescription.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.fundamental_domain_description : Ad3.R.D0 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain | exact GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain <;> assumption)
