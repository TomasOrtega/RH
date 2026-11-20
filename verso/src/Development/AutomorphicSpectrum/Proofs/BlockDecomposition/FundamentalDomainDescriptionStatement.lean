import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainDescription
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain | exact GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_ …`.
-/
theorem _root_.GlobalTheory.T.fundamental_domain_description : Ad3.R.D0 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain | exact GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain <;> assumption)
