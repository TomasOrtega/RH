import Mathlib
import Formalism.PeriodIntegrals.KerIso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelOrder.ValNatCastEqOne

/- English proof (translation)
The claim follows from `PI.KerIso.DetOrdW.detOrdIndep`.
-/
theorem ordRelativeDet_independence : PI.KerIso.DetOrdIndep :=
  PI.KerIso.DetOrdW.detOrdIndep
