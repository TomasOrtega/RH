import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootShift.CountD
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootShift.ArithP

/- English proof (translation)
The claim follows from `PI.SqfRootShift.W.claim_of PI.SqfRootShift.W.countP PI.SqfRootShift.W.arithP`.
-/
theorem squarefree_root_shift : PI.SqfRootShift.Claim :=
  PI.SqfRootShift.W.claim_of PI.SqfRootShift.W.countP PI.SqfRootShift.W.arithP
