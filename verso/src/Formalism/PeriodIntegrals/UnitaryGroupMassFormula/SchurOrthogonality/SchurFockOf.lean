import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.Assembly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.ConstructionA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.ConstructionB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.ConstructionC

noncomputable section

namespace PI.WSF

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem schurFock_of (h : PI.HwIrred) : PI.SchurFock :=
  schurFock_of_steps unitary_haar_measure (schurOrth_of h evaluation_at_one)

end PI.WSF
