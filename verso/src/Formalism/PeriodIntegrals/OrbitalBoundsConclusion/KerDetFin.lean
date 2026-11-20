import Mathlib
import Formalism.PeriodIntegrals.KerIso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelFiniteness.ExistsDenomBackward

/- English proof (translation)
The claim follows from `PI.KerDetFinW.detOrdFin`.
-/
theorem ordRelativeDet_finite : PI.KerIso.DetOrdFin := PI.KerDetFinW.detOrdFin
