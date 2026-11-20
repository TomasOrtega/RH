import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedRankinSelbergLocalFactor
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnramifiedRankinSelbergLocalFactor.lean&line=387#L387)
-/
theorem _root_.GlobalTheory.T.unramified_rankin_selberg_local_factor : Ad3.Loc2 → Ad3.R.E4 := by
  first | exact @GlobalTheory.CompanionTheory.RSUnram.rankinSelberg_unramified | exact GlobalTheory.CompanionTheory.RSUnram.rankinSelberg_unramified | (intros; apply GlobalTheory.CompanionTheory.RSUnram.rankinSelberg_unramified <;> assumption)
