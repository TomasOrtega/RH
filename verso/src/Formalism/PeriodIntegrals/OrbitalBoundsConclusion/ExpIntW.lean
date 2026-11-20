import Formalism.PeriodIntegrals.ExpIntW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.InvNatMemWf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.StepIII
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.RootsOfUnityRingLeWittIntegers

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem expIntegralWitt : PI.ExpIntW :=
  PI.ExpIntWProof.expIntW_of_key PI.ExpIntWProof.stepI PI.ExpIntWProof.keyW
