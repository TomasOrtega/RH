import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SqPairLocalOfSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.MemFixSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.ExistsDenFg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.IsUnitIffSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.ExistsConjugationFixedUniformizer
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.DetectIdeal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.IsUnimodularOfIsSDG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.DivAtOneOfInt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.IsMaximalComapCj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SplitPlaceOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.Imports

namespace PI.SqPairLocal

/- English proof (translation)
The claim follows from `modelEx_of fixedDVR realUnif`.
-/
theorem modelEx : ModelEx := modelEx_of fixedDVR realUnif

/- English proof (translation)
The claim follows from `sqPairLocal_of_steps h locGlob intMul (glue_of powLoc) (splitPlace_of powLoc) inertAsm modelEx dict locMat powLoc`.
-/
theorem sqPairLocal_of (h : PI.SqPair.LocCartanPair) : PI.SqPair.PLocalAll :=
  sqPairLocal_of_steps h locGlob intMul (glue_of powLoc) (splitPlace_of powLoc) inertAsm modelEx dict locMat
    powLoc

end PI.SqPairLocal
