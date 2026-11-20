import Mathlib
import Formalism.PeriodIntegrals.UnitDetRoot
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.Partial
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobFin

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unit_det_root_of_unity : PI.UnitDetRoot :=
  PI.UnitaryGroupMassFormula.UnitDetRoot.unitDetRoot_of_global PI.UnitaryGroupMassFormula.UnitDetRoot.globalLUnit
