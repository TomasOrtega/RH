import Formalism.PeriodIntegrals.PrimeSums
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MertensLogSum.PrimeLogOverPTop

/- English proof (translation)
The claim follows from `PI.PrimeLogOverPWork.sum_log_div_prime_le`.
-/
theorem sum_log_p_over_p : PI.PrimeLogOverP := PI.PrimeLogOverPWork.sum_log_div_prime_le
