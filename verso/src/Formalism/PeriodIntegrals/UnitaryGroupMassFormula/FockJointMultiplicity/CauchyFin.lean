import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyHWOfShape
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauBFin

namespace PI.FJM

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cauchy_highest_weight : CauchyHW :=
  PI.FJMB.cauchyHW_of_shape PI.FJMX.minorProductDiagonal

end PI.FJM
