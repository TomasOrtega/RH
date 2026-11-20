import Mathlib
import Formalism.PeriodIntegrals.ContractionsCovariantIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.QnCovHat2OfLin

/- English proof (translation)
The claim follows from `PI.QnCovHat2W.qnCovHat2_of_lin`.
-/
theorem covariant_hat_sq_of_lin : PI.QnCovLin → PI.QnCovHat2 := PI.QnCovHat2W.qnCovHat2_of_lin
