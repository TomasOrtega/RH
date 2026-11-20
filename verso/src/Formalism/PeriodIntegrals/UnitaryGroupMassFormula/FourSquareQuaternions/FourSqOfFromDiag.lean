import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FourSquareQuaternions.OrthogonalDiagonal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FourSquareQuaternions.QmapInjective

namespace PI.KerIso.FourSqW

/- English proof (translation)
The claim follows from `fourSq_of orthogonal_diagonal from_diagonal`.
-/
theorem main : FourSq := fourSq_of orthogonal_diagonal from_diagonal

end PI.KerIso.FourSqW
