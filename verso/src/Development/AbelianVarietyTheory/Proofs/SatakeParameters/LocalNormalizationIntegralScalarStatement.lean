import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalizationIntegralScalar
import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.localNormalization_integral_scalar : Formalism.L2.AlgTh.LocNormScale := by
  first | exact @GlobalTheory.locNormScale | exact GlobalTheory.locNormScale | (intros; apply GlobalTheory.locNormScale <;> assumption)
