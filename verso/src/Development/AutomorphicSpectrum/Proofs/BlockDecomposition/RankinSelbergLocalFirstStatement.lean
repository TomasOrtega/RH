import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalFirst
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RankinSelbergRotation.a1 | exact GlobalTheory.CompanionTheory.RankinSelbergRotation.a1 | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergRotation.a1 <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.rankin_selberg_local_first : Ad3.R.A1 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergRotation.a1 | exact GlobalTheory.CompanionTheory.RankinSelbergRotation.a1 | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergRotation.a1 <;> assumption)
