import Mathlib
import Formalism.PeriodIntegrals.MirabIndex
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicIndex.RowMulOfMirab

/- English proof (translation)
The claim follows from `PI.MirabolicIndex₂.mirabIndex`.
-/
theorem mirabolic_index : PI.MirabIndex.MirabIndex := PI.MirabolicIndex₂.mirabIndex
