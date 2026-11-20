import Mathlib
import Formalism.PeriodIntegrals.KerIso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConstantCoefficientKernel.RingHomCoeffZero

/- English proof (translation)
The claim follows from `PI.KerExtCWork.extC`.
-/
theorem kernel_extension_c : PI.KerIso.ExtC := PI.KerExtCWork.extC
