import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalNonvanishing
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RSNonvanish.rankin_selberg_nonvanishing_of_whittaker` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRankinSelbergLocalNonvanishing.lean&line=426#L426)
-/
theorem _root_.GlobalTheory.T.rankin_selberg_local_nonvanishing : Ad3.Loc2 → Ad3.R.A10 → Ad3.R.A11 := by
  first | exact @GlobalTheory.CompanionTheory.RSNonvanish.rankin_selberg_nonvanishing_of_whittaker | exact GlobalTheory.CompanionTheory.RSNonvanish.rankin_selberg_nonvanishing_of_whittaker | (intros; apply GlobalTheory.CompanionTheory.RSNonvanish.rankin_selberg_nonvanishing_of_whittaker <;> assumption)
