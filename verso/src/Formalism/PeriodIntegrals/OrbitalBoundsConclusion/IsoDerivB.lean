import Mathlib
import Formalism.PeriodIntegrals.IsoDerivB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.IsoDerivB

/- English proof (translation)
The claim follows from `PI.IsoDerivBFintype.isoDerivB`.
-/
theorem isometry_derivative_bound : PI.IsoDerivB.IsoDerivB := PI.IsoDerivBFintype.isoDerivB
