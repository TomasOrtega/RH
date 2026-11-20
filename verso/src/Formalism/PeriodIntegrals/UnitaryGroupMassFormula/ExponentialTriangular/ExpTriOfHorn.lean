import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.ExpTriOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.SpecExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.PsumEqRange

namespace PI.ET

/- English proof (translation)
The claim follows from `expTri_of specExists hsEq hH abelSq euclTri`.
-/
theorem expTri_of_horn (hH : Horn) : PI.ExpTri :=
  expTri_of specExists hsEq hH abelSq euclTri

end PI.ET
