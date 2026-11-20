import Formalism.PeriodIntegrals.ExpIntW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.InvNatMemWf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.StepIII
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.RootsOfUnityRingLeWittIntegers

/- English proof (translation)
The claim follows from `PI.ExpIntWProof.expIntW_of_key PI.ExpIntWProof.stepI PI.ExpIntWProof.keyW`.
-/
theorem expIntegralWitt : PI.ExpIntW :=
  PI.ExpIntWProof.expIntW_of_key PI.ExpIntWProof.stepI PI.ExpIntWProof.keyW
