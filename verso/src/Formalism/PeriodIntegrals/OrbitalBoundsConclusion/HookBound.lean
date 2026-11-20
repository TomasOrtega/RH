import Mathlib
import Formalism.PeriodIntegrals.HookBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.CapelliOps

/- English proof (translation)
The claim follows from `PI.HookSteps.hookBound_of PI.HookSteps.Cap.capelli_determinant_identity`.
-/
theorem hook_length_bound : PI.HookBound := PI.HookSteps.hookBound_of PI.HookSteps.Cap.capelli_determinant_identity
