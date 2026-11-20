import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelCharacter
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNewformLiftLevelCharacter.lean&line=160#L160)
-/
theorem _root_.GlobalTheory.T.newform_lift_level_character : Ad3.R.B0 → Ad3.R.AutomorphicLevelEquivariance := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance | exact GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance <;> assumption)
