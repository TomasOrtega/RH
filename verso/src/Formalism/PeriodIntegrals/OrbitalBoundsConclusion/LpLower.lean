import Mathlib
import Formalism.PeriodIntegrals.LpLower
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LinearProgramLowerBound.LpFeasibleLe

/- English proof (translation)
The claim follows from `PI.lpLower_main`.
-/
theorem lp_lower_bound : PI.LpLower := PI.lpLower_main
