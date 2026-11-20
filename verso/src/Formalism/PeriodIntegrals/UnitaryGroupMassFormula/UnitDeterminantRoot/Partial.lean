import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.UnitDetRootOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.NormLeOneOfRoot
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.NsmulRelIdxMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.DetMemOfEntries

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitDetRoot_of_global (h : GlobalLUnit) : PI.UnitDetRoot :=
  unitDetRoot_of detInK localStd h normOne rootStep conjMem conjLUnit

end PI.UnitaryGroupMassFormula.UnitDetRoot
