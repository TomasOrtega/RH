import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalFirst
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RankinSelbergRotation.a1` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRankinSelbergLocalFirst.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.rankin_selberg_local_first : Ad3.R.A1 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergRotation.a1 | exact GlobalTheory.CompanionTheory.RankinSelbergRotation.a1 | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergRotation.a1 <;> assumption)
