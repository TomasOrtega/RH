import Mathlib
import Formalism.PeriodIntegrals.PowBddInt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.Imports
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.EvalIntMapEqZero

/- English proof (translation)
The claim follows from `PI.PowBddIntWork.powBddInt_of PI.PowBddIntWork.stepA PI.PowBddIntWork.stepB`.
-/
theorem power_bounded_integral : PI.PowBddInt :=
  PI.PowBddIntWork.powBddInt_of PI.PowBddIntWork.stepA PI.PowBddIntWork.stepB
