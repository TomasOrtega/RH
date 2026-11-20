import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantDeterminantScaling.IntCastMulEqSmul

/- English proof (translation)
The claim follows from `PI.QnCovDetW.qnCovDet_of_lin`.
-/
theorem covariant_det_of_lin : PI.QnCovLin → PI.QnCovDet :=
  PI.QnCovDetW.qnCovDet_of_lin
