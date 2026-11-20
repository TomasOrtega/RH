import Mathlib
import Formalism.PeriodIntegrals.UnitDetRoot
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.Partial
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobFin

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.UnitDetRoot.unitDetRoot_of_global PI.UnitaryGroupMassFormula.UnitDetRoot.globalLUnit`.
-/
theorem unit_det_root_of_unity : PI.UnitDetRoot :=
  PI.UnitaryGroupMassFormula.UnitDetRoot.unitDetRoot_of_global PI.UnitaryGroupMassFormula.UnitDetRoot.globalLUnit
