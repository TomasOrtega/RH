import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalWhittaker
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.NewformLiftLocalWhittaker.f7` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNewformLiftLocalWhittaker.lean&line=431#L431)
-/
theorem _root_.GlobalTheory.T.newform_lift_local_whittaker : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.U0 → Ad3.R.U1 → Ad3.R.M0 → Ad3.R.M1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.F2 → Ad3.R.F3 → Ad3.R.F4 → Ad3.R.F7 := by
  first | exact @GlobalTheory.CompanionTheory.NewformLiftLocalWhittaker.f7 | exact GlobalTheory.CompanionTheory.NewformLiftLocalWhittaker.f7 | (intros; apply GlobalTheory.CompanionTheory.NewformLiftLocalWhittaker.f7 <;> assumption)
