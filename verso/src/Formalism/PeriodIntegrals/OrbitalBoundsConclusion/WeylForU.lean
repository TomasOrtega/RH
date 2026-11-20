import Mathlib
import Formalism.PeriodIntegrals.WeylForU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaUnitary.NatWCastReal

/- English proof (translation)
The claim follows from `PI.WeylForUWork.weylForU_of`.
-/
theorem weylForU_of : PI.ModelIso → PI.NablaDim → PI.WeylForU := PI.WeylForUWork.weylForU_of
