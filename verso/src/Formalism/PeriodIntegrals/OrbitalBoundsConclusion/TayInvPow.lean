import Formalism.PeriodIntegrals.TayInvPow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TaylorInversePower.SumMultinomialSub

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.TayInvPow.main`.
-/
theorem coeffInversePowerFacts.{u, v} : PI.TayInvPow.{u, v} := PI.UnitaryGroupMassFormula.TayInvPow.main
