import Mathlib
import Formalism.PeriodIntegrals.KerTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorSpanning.TensSpans

/- English proof (translation)
The claim follows from `PI.KerTens.W.tensSpans`.
-/
theorem kernel_tensor_spans : PI.KerTens.TensSpans := PI.KerTens.W.tensSpans
