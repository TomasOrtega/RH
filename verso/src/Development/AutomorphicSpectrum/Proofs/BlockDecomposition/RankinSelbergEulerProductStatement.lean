import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergEulerProduct
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRankinSelbergEulerProduct.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.rankin_selberg_euler_product : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.A10 → Ad3.R.E2 → Ad3.R.E3 → Ad3.R.E5 → Ad3.R.UnramifiedEulerProductIntegral → Ad3.R.F2 → Ad3.R.E6 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.Unfolded.e6 | exact GlobalTheory.CompanionTheory.RankinSelberg.Unfolded.e6 | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.Unfolded.e6 <;> assumption)
