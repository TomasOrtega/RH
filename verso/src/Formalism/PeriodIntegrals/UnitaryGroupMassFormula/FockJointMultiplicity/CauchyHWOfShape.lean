import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyHighestWeightOfShape
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.DiagonalImageBlockFree

namespace PI.FJMB

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cauchyHW_of_shape (hS : HypShape) : PI.FJM.CauchyHW :=
  cauchy_highest_weight_of_shape hS diagonal_hypothesis diagonal_image_block_free

end PI.FJMB
