import Mathlib
import Formalism.PeriodIntegrals.LowCyc
import Formalism.PeriodIntegrals.KFinSmooth
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem low_smooth_of_k_finite : PI.KFinSmooth → PI.LowSmooth := PI.UnitaryGroupMassFormula.LowSmooth.lowSmooth_of_kFinSmooth
