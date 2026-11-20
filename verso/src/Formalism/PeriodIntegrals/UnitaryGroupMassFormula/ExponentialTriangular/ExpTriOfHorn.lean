import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.ExpTriOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.SpecExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.PsumEqRange

namespace PI.ET

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem expTri_of_horn (hH : Horn) : PI.ExpTri :=
  expTri_of specExists hsEq hH abelSq euclTri

end PI.ET
