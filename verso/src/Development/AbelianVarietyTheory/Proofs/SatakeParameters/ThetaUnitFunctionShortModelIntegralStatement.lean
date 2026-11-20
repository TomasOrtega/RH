import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaUnitFunctionShortModelIntegral
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.thetaUnitFunction_shortModel_integral : Formalism.L2.KerInert.BeCob.ThetaTie := by
  first | exact @GlobalTheory.ShortModelTheta.thetaTie_holds | exact GlobalTheory.ShortModelTheta.thetaTie_holds | (intros; apply GlobalTheory.ShortModelTheta.thetaTie_holds <;> assumption)
