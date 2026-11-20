import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCentralInvariance
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RS.rankinSelberg_measure_facts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFundamentalDomainIntegralCentralInvariance.lean&line=370#L370)
-/
theorem _root_.GlobalTheory.T.fundamental_domain_integral_central_invariance : Ad3.R.G1a := by
  first | exact @GlobalTheory.CompanionTheory.RS.rankinSelberg_measure_facts | exact GlobalTheory.CompanionTheory.RS.rankinSelberg_measure_facts | (intros; apply GlobalTheory.CompanionTheory.RS.rankinSelberg_measure_facts <;> assumption)
