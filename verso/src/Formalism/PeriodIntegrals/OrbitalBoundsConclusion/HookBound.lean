import Mathlib
import Formalism.PeriodIntegrals.HookBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.CapelliOps

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hook_length_bound : PI.HookBound := PI.HookSteps.hookBound_of PI.HookSteps.Cap.capelli_determinant_identity
