import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergSeventhOfSecond
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRankinSelbergSeventhOfSecond.lean&line=169#L169)
-/
theorem _root_.GlobalTheory.T.rankin_selberg_seventh_of_second : Ad3.R.A2 → Ad3.R.A7 := by
  first | exact @GlobalTheory.CompanionTheory.RSPlane.a7 | exact GlobalTheory.CompanionTheory.RSPlane.a7 | (intros; apply GlobalTheory.CompanionTheory.RSPlane.a7 <;> assumption)
