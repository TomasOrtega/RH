import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatDecomposition.SkipOneEqSuccAbove

/- English proof (translation)
The claim follows from `PI.QnCovHatW.qnCovHat_of_lin`.
-/
theorem covariant_hat_of_lin : PI.QnCovLin → PI.QnCovHat :=
  PI.QnCovHatW.qnCovHat_of_lin
