import Formalism.PeriodIntegrals.UJClassMassAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UnitaryClassMass

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.UJClassMass.unitary_class_mass`.
-/
theorem unitary_class_mass_hermitian : PI.UJClassMass2.UJClassMass :=
  PI.UnitaryGroupMassFormula.UJClassMass.unitary_class_mass
