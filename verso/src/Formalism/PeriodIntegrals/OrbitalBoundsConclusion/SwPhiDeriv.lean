import Mathlib
import Formalism.PeriodIntegrals.LongWeylElementSquare
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PhiDerivative.StarinvDeriv

/- English proof (translation)
Introduce `k r` and use `PI.SwBig.PhiDerivW.main k r hW`.
-/
theorem phiDeriv_of (hW : PI.SwBig.LongWeylElementSquare) : PI.SwBig.PhiDeriv :=
  fun k r => PI.SwBig.PhiDerivW.main k r hW
