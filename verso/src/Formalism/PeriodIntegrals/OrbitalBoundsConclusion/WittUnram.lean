import Mathlib
import Formalism.PeriodIntegrals.WittUnram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittUnramified.WittUnramMain

/- English proof (translation)
The claim follows from `PI.WittUnramWork.wittUnram_main`.
-/
theorem witt_unramified : PI.WittUnram :=
  PI.WittUnramWork.wittUnram_main
