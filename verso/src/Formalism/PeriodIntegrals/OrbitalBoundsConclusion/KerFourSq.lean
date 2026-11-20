import Mathlib
import Formalism.PeriodIntegrals.KerIso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FourSquareQuaternions.FourSqOfFromDiag

/- English proof (translation)
The claim follows from `PI.KerIso.FourSqW.main`.
-/
theorem kernel_four_squares : PI.KerIso.FourSq :=
  PI.KerIso.FourSqW.main
