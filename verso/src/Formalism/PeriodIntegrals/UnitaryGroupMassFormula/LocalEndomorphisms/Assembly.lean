import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.LocalEndHomeoOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.IsUniformInducingOfVal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.AlgebraMapMemRange

namespace PI.LocalEndW

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem localEndHomeo_of_three (hA : HenselRoot) (hB1 : IntOfHensel) (hB2 : ValOfInt) :
    PI.LocalEndHomeo :=
  localEndHomeo_of hA hB1 hB2 valContinuous valSurjective

end PI.LocalEndW
