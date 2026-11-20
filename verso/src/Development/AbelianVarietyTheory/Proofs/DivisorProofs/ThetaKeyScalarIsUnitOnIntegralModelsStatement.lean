import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyScalarIsUnitOnIntegralModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.thetaKeyScalar_isUnit_on_integralModels : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.KeyUnitOnModels := by
  first | exact @GlobalTheory.KeyUnitModels.keyUnitOnModels | exact GlobalTheory.KeyUnitModels.keyUnitOnModels | (intros; apply GlobalTheory.KeyUnitModels.keyUnitOnModels <;> assumption)
