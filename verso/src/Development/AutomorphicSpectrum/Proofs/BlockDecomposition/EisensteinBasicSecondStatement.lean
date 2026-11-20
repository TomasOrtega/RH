import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicSecond
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEisensteinBasicSecond.lean&line=154#L154)
-/
theorem _root_.GlobalTheory.T.eisenstein_basic_second : Ad3.R.B0 → Ad3.R.E2 := by
  first | exact @GlobalTheory.CompanionTheory.RankinEuler.e2 | exact GlobalTheory.CompanionTheory.RankinEuler.e2 | (intros; apply GlobalTheory.CompanionTheory.RankinEuler.e2 <;> assumption)
