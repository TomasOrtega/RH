import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.UnitsOpenTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstTestOfPolarWh
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibOrbP
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibAllP

namespace PI.AprimeInfW

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem unitsOpenTens : UnitsOpenTens := fun X => isOpen_units_tens X

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fibOrbAt_of_compact (hC : MassDataMassesW.HinfCompact) : FibOrbAt :=
  fibOrbAt_of unitsOpenTens fibAllT_holds hC

end PI.AprimeInfW
