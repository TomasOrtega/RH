import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.SqfDivDegOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.FibreNonempty

namespace PI.SqfDivDeg.W

/- English proof (translation)
The claim follows from `sqfDivDeg_of hA mainCount`.
-/
theorem sqfDivDeg_of_rootDense (hA : RootDense) : PI.SqfDivDeg.Claim :=
  sqfDivDeg_of hA mainCount

end PI.SqfDivDeg.W
