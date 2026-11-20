import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalFourth
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.rankin_selberg_local_fourth : Ad3.R.A4 := by
  first | exact @GlobalTheory.CompanionTheory.RankinKernel.kernel_integrable | exact GlobalTheory.CompanionTheory.RankinKernel.kernel_integrable | (intros; apply GlobalTheory.CompanionTheory.RankinKernel.kernel_integrable <;> assumption)
