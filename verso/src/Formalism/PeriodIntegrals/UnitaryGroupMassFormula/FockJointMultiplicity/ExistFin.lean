import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.IsDiagonalBlockIndexRightOfPositiveRoot
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.LoweringPartRightActionInlInr

namespace PI.FJMX

/- English proof (translation)
The claim follows from `vecHW1_of PI.FJM.leftDiagonalActionFormula PI.FJM.leftOffDiagonalActionFormula`.
-/
theorem shapeVectorLeftHighestWeight : PI.FJM.VecHW1 := vecHW1_of PI.FJM.leftDiagonalActionFormula PI.FJM.leftOffDiagonalActionFormula

/- English proof (translation)
The claim follows from `vecHW2_of PI.FJM.rightDiagonalActionFormula PI.FJM.rightOffDiagonalActionFormula`.
-/
theorem shapeVectorRightHighestWeight : PI.FJM.VecHW2 := vecHW2_of PI.FJM.rightDiagonalActionFormula PI.FJM.rightOffDiagonalActionFormula

end PI.FJMX
