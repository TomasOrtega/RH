import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.IoXiHw
import Formalism.PeriodIntegrals.HwIrred
import Formalism.PeriodIntegrals.GTBranch

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

/- English proof (translation)
The claim follows from `ioExists_of' h3 h4 hx`.
-/
theorem ioExists_of (h3 : PI.HwIrred) (h4 : PI.GTBranch) (hx : XiFacts) : IoExists :=
  ioExists_of' h3 h4 hx

end PI.WGL
