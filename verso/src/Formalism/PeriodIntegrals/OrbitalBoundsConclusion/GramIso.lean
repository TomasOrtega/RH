import Mathlib
import Formalism.PeriodIntegrals.FglGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramIsometryCoefficient.ExCoeffOneNe

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.GramIso.gramIso`.
-/
theorem flag_gram_iso : PI.FglGram.GramIso := PI.UnitaryGroupMassFormula.GramIso.gramIso
