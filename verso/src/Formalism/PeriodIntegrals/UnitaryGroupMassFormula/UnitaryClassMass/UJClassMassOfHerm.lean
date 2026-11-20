import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PPatchF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PLatStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfOpen

namespace PI.UnitaryGroupMassFormula.UJClassMass

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem surjStep_of_herm' (hH : HermApprox) : SurjStep := surjStep_of_herm hH lsOne

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uJClassMass_of_herm (hH : HermApprox) : PI.UJClassMass2.UJClassMass :=
  uJClassMass_of_open lattice_modification (surjStep_of_herm' hH)

end PI.UnitaryGroupMassFormula.UJClassMass
