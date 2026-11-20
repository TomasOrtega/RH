import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftExistence
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RankinSelbergQ.f0 | exact GlobalTheory.CompanionTheory.RankinSelbergQ.f0 | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergQ.f0 <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.newform_lift_existence : Ad3.R.B0 → Ad3.R.F0 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergQ.f0 | exact GlobalTheory.CompanionTheory.RankinSelbergQ.f0 | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergQ.f0 <;> assumption)
