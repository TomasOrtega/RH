import Mathlib
import Formalism.PeriodIntegrals.LowCyc
import Formalism.PeriodIntegrals.KFinSmooth
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.LowSmooth.lowSmooth_of_kFinSmooth`.
-/
theorem low_smooth_of_k_finite : PI.KFinSmooth → PI.LowSmooth := PI.UnitaryGroupMassFormula.LowSmooth.lowSmooth_of_kFinSmooth
