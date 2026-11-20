import Mathlib
import Formalism.PeriodIntegrals.FglGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramUnitMultiplication.BeMulByZero

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.GramUnit.gramUnit`.
-/
theorem gramExpansion_orthonormal : PI.FglGram.GramUnit := PI.UnitaryGroupMassFormula.GramUnit.gramUnit
