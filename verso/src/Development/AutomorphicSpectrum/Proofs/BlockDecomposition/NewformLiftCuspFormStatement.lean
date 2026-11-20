import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftCuspForm
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LiftCusp.lift_cuspidal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNewformLiftCuspForm.lean&line=449#L449)
-/
theorem _root_.GlobalTheory.T.newform_lift_cusp_form : Ad3.R.B0 → Ad3.R.ConstantTermVanishingAlt := by
  first | exact @GlobalTheory.CompanionTheory.LiftCusp.lift_cuspidal | exact GlobalTheory.CompanionTheory.LiftCusp.lift_cuspidal | (intros; apply GlobalTheory.CompanionTheory.LiftCusp.lift_cuspidal <;> assumption)
