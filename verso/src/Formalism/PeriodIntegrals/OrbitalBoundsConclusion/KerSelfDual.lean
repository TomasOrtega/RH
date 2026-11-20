import Mathlib
import Formalism.PeriodIntegrals.SelfDualOfDiff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualDifferent.SelfDualOfDiff

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.KerSelfDual.selfDualOfDiff`.
-/
theorem kernel_self_dual_of_different : PI.KerIso.SelfDualOfDiff := PI.UnitaryGroupMassFormula.KerSelfDual.selfDualOfDiff
