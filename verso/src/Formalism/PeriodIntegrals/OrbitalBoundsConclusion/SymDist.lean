import Mathlib
import Formalism.PeriodIntegrals.SymDist
import Formalism.PeriodIntegrals.ExpTri
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SymmetricDistance.SymDistOf

/- English proof (translation)
The claim follows from `PI.SymDistWork.symDist_of`.
-/
theorem symDist_of : PI.ExpTri → PI.SymDist := PI.SymDistWork.symDist_of
