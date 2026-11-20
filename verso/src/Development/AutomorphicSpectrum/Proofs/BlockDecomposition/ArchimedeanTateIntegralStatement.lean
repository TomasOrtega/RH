import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanTateIntegral
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.archimedean_tate_integral : Ad3.LR.C.TateInt := by
  first | exact @GlobalTheory.CompanionTheory.RealTateConv.tateInt | exact GlobalTheory.CompanionTheory.RealTateConv.tateInt | (intros; apply GlobalTheory.CompanionTheory.RealTateConv.tateInt <;> assumption)
