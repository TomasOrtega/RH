import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftConductor
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNewformLiftConductor.lean&line=401#L401)
-/
theorem _root_.GlobalTheory.T.newform_lift_conductor : Ad3.R.B0 → Ad3.R.F0b := by
  first | exact @GlobalTheory.CompanionTheory.NewformLiftConductor.f0b | exact GlobalTheory.CompanionTheory.NewformLiftConductor.f0b | (intros; apply GlobalTheory.CompanionTheory.NewformLiftConductor.f0b <;> assumption)
