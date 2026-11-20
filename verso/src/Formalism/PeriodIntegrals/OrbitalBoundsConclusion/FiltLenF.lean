import Mathlib
import Formalism.PeriodIntegrals.FiltLen
import Formalism.PeriodIntegrals.FiltLenF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiltrationLength.FiltLenFMain

/- English proof (translation)
The claim follows from `PI.FiltrationLength.filtLenF_main`.
-/
theorem filtration_length_bound : PI.FiltLenF := PI.FiltrationLength.filtLenF_main
