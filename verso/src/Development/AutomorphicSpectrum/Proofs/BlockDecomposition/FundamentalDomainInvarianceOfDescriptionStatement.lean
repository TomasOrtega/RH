import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainInvarianceOfDescription
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFundamentalDomainInvarianceOfDescription.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.fundamental_domain_invariance_of_description : Ad3.R.D0 → Ad3.R.G0 := by
  first | exact @GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain | exact GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain | (intros; apply GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain <;> assumption)
