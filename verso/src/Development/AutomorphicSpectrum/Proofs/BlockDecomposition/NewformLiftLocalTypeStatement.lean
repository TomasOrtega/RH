import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalType
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNewformLiftLocalType.lean&line=394#L394)
-/
theorem _root_.GlobalTheory.T.newform_lift_local_type : Ad3.R.B0 → Ad3.R.HeckeSumLocalTranslates := by
  first | exact @GlobalTheory.CompanionTheory.RSq.f3a | exact GlobalTheory.CompanionTheory.RSq.f3a | (intros; apply GlobalTheory.CompanionTheory.RSq.f3a <;> assumption)
