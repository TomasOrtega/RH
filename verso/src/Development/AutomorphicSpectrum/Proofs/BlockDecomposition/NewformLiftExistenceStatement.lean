import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftExistence
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNewformLiftExistence.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.newform_lift_existence : Ad3.R.B0 → Ad3.R.F0 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergQ.f0 | exact GlobalTheory.CompanionTheory.RankinSelbergQ.f0 | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergQ.f0 <;> assumption)
