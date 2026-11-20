import Mathlib
import Formalism.PeriodIntegrals.ZerosWindow
import Formalism.PeriodIntegrals.ZerosWindowIn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.Transfer

/- English proof (translation)
Introduce `hL hZ hI` and use `PI.ZW.zerosWindow_of_transfer PI.ZW.transfer hL hZ hI`.
-/
theorem zerosWindow_of : PI.LBoundRight → PI.ZetaBoundRight → PI.LInvRight → PI.ZerosWindow :=
  fun hL hZ hI => PI.ZW.zerosWindow_of_transfer PI.ZW.transfer hL hZ hI
