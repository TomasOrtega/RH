import Mathlib
import Formalism.PeriodIntegrals.SqfDivDeg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.CardMonicTwoRootsLe

/- English proof (translation)
The claim follows from `PI.SqfDivDeg.W.sqfDivDeg_of_rootDense PI.SqfDivDeg.W.rootDense`.
-/
theorem squarefree_div_degree : PI.SqfDivDeg.Claim :=
  PI.SqfDivDeg.W.sqfDivDeg_of_rootDense PI.SqfDivDeg.W.rootDense
