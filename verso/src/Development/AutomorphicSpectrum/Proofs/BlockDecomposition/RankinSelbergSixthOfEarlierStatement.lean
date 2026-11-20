import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergSixthOfEarlier
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRankinSelbergSixthOfEarlier.lean&line=478#L478)
-/
theorem _root_.GlobalTheory.T.rankin_selberg_sixth_of_earlier : Ad3.R.A1 → Ad3.R.A3 → Ad3.R.A4 → Ad3.R.A5 → Ad3.R.A6 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.Trilinear.zv_eq_trilinear | exact GlobalTheory.CompanionTheory.RankinSelberg.Trilinear.zv_eq_trilinear | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.Trilinear.zv_eq_trilinear <;> assumption)
