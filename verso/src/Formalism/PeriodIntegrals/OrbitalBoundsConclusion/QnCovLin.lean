import Mathlib
import Formalism.PeriodIntegrals.ContractionsCovariantIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantLinearProduct.OfFnProdSmul

/- English proof (translation)
The claim follows from `PI.QnCovLinW.qnCovLin`.
-/
theorem covariant_linear : PI.QnCovLin :=
  PI.QnCovLinW.qnCovLin
