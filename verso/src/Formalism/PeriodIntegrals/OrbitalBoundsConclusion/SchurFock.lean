import Formalism.PeriodIntegrals.SchurFock
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.SchurFockOf

/- English proof (translation)
The claim follows from `PI.WSF.schurFock_of highest_weight_irreducible`.
-/
theorem schur_fock : PI.SchurFock := PI.WSF.schurFock_of highest_weight_irreducible
