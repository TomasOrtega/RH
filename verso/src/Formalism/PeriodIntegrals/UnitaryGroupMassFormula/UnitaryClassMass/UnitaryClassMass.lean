import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfHerm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermCL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermXB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LocalIntegralOfSubstitution
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.TcoordBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LatticesCloseLocally

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tensor_localization : TensLoc := tensLocX_of local_integral_of_substitution

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hermitian_approximation : HermApprox :=
  hermitian_approximation_of_parts local_switching_lattice tensor_localization lattices_close_locally wPlace bcU gramOK

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitary_class_mass : PI.UJClassMass2.UJClassMass :=
  uJClassMass_of_herm hermitian_approximation

set_option pp.fullNames true in
#check @PI.UnitaryGroupMassFormula.UJClassMass.hermitian_approximation
set_option pp.fullNames true in
#check @PI.UnitaryGroupMassFormula.UJClassMass.unitary_class_mass
#print axioms PI.UnitaryGroupMassFormula.UJClassMass.tensor_localization
#print axioms PI.UnitaryGroupMassFormula.UJClassMass.hermitian_approximation
#print axioms PI.UnitaryGroupMassFormula.UJClassMass.unitary_class_mass

end PI.UnitaryGroupMassFormula.UJClassMass

end
