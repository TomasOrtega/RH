import Mathlib
import Formalism.PeriodIntegrals.InertPrime
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeJacobi.NotIsSquareOfJacobi

open NumberField

/- English proof (translation)
Introduce `K _ _ hK b d p hb hp hj`. Conclude with `PI.InertPrimeWork.inert K hK b d p hb hp hj`.
-/
theorem isPrime_span_of_jacobi_neg_one : PI.InertPrime := by
  intro K _ _ hK b d p hb hp hj
  exact PI.InertPrimeWork.inert K hK b d p hb hp hj
