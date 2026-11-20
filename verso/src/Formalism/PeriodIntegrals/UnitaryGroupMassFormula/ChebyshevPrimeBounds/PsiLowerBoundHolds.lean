import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PrimeCountBoundOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.LogFactorialEqSumOfLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.LogFactorialLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PsiUpperBoundOfLtThirtyMulSixPow

namespace PI.PC

/- English proof (translation)
The claim follows from `chUpper_of chebyshevConstantNumeric dUpper sandwich`.
-/
theorem psiUpperBound_holds : CHUpper := chUpper_of chebyshevConstantNumeric dUpper sandwich

/- English proof (translation)
The claim follows from `chLower_of chebyshevConstantNumeric dLower sandwich`.
-/
theorem psiLowerBound_holds : CHLower := chLower_of chebyshevConstantNumeric dLower sandwich

end PI.PC
