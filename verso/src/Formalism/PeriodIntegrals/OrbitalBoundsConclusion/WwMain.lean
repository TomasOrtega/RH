import Mathlib
import Formalism.PeriodIntegrals.WwMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.InfinitePadicComplex
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.LfunEqOfSubset
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.SumInjEqSumPairs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.DeXCBOf

/- English proof (translation)
The claim follows from `PI.WwMainW.wwMain_of PI.WwMainW.evalH PI.WwMainW.lH PI.WwMainW.lLin (PI.WwMainW.deXCB_of PI.WwMainW.cbSorted)`.
-/
theorem minor_identity : PI.WwMain.WwMain :=
  PI.WwMainW.wwMain_of PI.WwMainW.evalH PI.WwMainW.lH PI.WwMainW.lLin
    (PI.WwMainW.deXCB_of PI.WwMainW.cbSorted)
