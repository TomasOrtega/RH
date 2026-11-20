import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanLocalIntegral
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FArchimedeanLocalIntegral.lean&line=371#L371)
-/
theorem _root_.GlobalTheory.T.archimedean_local_integral : Ad3.R.E5 := by
  first | exact @GlobalTheory.CompanionTheory.RealArchimedeanCharacter.E5 | exact GlobalTheory.CompanionTheory.RealArchimedeanCharacter.E5 | (intros; apply GlobalTheory.CompanionTheory.RealArchimedeanCharacter.E5 <;> assumption)
