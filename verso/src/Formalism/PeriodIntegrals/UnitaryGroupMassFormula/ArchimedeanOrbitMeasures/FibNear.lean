import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.UnitsOpenTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstTestOfPolarWh
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibOrbP
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibAllP

namespace PI.AprimeInfW

/- English proof (translation)
Introduce `X` and use `isOpen_units_tens X`.
-/
theorem unitsOpenTens : UnitsOpenTens := fun X => isOpen_units_tens X

/- English proof (translation)
The claim follows from `fibOrbAt_of unitsOpenTens fibAllT_holds hC`.
-/
theorem fibOrbAt_of_compact (hC : MassDataMassesW.HinfCompact) : FibOrbAt :=
  fibOrbAt_of unitsOpenTens fibAllT_holds hC

end PI.AprimeInfW
