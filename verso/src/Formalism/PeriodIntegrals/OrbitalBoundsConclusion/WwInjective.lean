import Mathlib
import Formalism.PeriodIntegrals.WwInjective
import Formalism.PeriodIntegrals.WwCauchyBinet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramInjectivity.InstFintypeColChoice

/- English proof (translation)
The claim follows from `PI.WwInjectiveWork.wwInjective_of h`.
-/
theorem wwInjective_of (h : PI.WwCauchyBinet.WwCauchyBinet) : PI.WwInjective.WwInjective :=
  PI.WwInjectiveWork.wwInjective_of h
