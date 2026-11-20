import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergUnfolding
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRankinSelbergUnfolding.lean&line=127#L127)
-/
theorem _root_.GlobalTheory.T.rankin_selberg_unfolding : Ad3.R.G2a → Ad3.R.G2b → Ad3.R.G3a → Ad3.R.G3 := by
  first | exact @GlobalTheory.CompanionTheory.BottomRowCoordinates.g3 | exact GlobalTheory.CompanionTheory.BottomRowCoordinates.g3 | (intros; apply GlobalTheory.CompanionTheory.BottomRowCoordinates.g3 <;> assumption)
