import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalSecond
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RSLocal.a2 | exact GlobalTheory.CompanionTheory.RSLocal.a2 | (intros; apply GlobalTheory.CompanionTheory.RSLocal.a2 <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.rankin_selberg_local_second : Ad3.R.A2 := by
  first | exact @GlobalTheory.CompanionTheory.RSLocal.a2 | exact GlobalTheory.CompanionTheory.RSLocal.a2 | (intros; apply GlobalTheory.CompanionTheory.RSLocal.a2 <;> assumption)
