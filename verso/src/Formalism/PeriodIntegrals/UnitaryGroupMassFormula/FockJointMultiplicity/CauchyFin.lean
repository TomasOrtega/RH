import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyHWOfShape
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauBFin

namespace PI.FJM

/- English proof (translation)
The claim follows from `PI.FJMB.cauchyHW_of_shape PI.FJMX.minorProductDiagonal`.
-/
theorem cauchy_highest_weight : CauchyHW :=
  PI.FJMB.cauchyHW_of_shape PI.FJMX.minorProductDiagonal

end PI.FJM
