import Mathlib
import Formalism.PeriodIntegrals.ZerosWindow
import Formalism.PeriodIntegrals.ZerosWindowIn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.Transfer

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem zerosWindow_of : PI.LBoundRight → PI.ZetaBoundRight → PI.LInvRight → PI.ZerosWindow :=
  fun hL hZ hI => PI.ZW.zerosWindow_of_transfer PI.ZW.transfer hL hZ hI
