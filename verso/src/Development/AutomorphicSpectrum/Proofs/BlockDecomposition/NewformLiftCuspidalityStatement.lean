import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftCuspidality
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.NewformLiftCuspidality.f6` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNewformLiftCuspidality.lean&line=361#L361)
-/
theorem _root_.GlobalTheory.T.newform_lift_cuspidality : Ad3.R.F6 := by
  first | exact @GlobalTheory.CompanionTheory.NewformLiftCuspidality.f6 | exact GlobalTheory.CompanionTheory.NewformLiftCuspidality.f6 | (intros; apply GlobalTheory.CompanionTheory.NewformLiftCuspidality.f6 <;> assumption)
