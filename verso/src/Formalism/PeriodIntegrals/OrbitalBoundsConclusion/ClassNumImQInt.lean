import Mathlib
import Formalism.PeriodIntegrals.ClassNumImQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ClassNumberIntegrality.HalfIntegral

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.ClassNumImQInt.intBasis`.
-/
theorem imag_quadratic_integral_basis : PI.ClassNumImQ.IntBasis :=
  PI.UnitaryGroupMassFormula.ClassNumImQInt.intBasis
