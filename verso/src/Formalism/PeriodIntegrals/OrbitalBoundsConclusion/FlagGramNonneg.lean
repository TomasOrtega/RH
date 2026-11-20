import Mathlib
import Formalism.PeriodIntegrals.FlagGramNonneg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.Gval

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.FlagGramNonneg.main`.
-/
theorem flag_gram_nonneg : PI.FlagGramNonneg := PI.UnitaryGroupMassFormula.FlagGramNonneg.main
