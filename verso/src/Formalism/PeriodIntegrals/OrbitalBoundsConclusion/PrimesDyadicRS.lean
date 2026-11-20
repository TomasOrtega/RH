import Mathlib
import Formalism.PeriodIntegrals.PrimesDyadicRS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.ClaimOfTwo
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.RealIneq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.SmallNaturalNumbersBound

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem primes_dyadic_range : PI.PrimesDyadicRS.Claim :=
  PI.PrimesDyadicRS.W.claim_of_two PI.PrimesDyadicRS.K.small_natural_numbers_bound PI.PrimesDyadicRS.W.real_dyadic_inequality
