import Mathlib
import Formalism.PeriodIntegrals.BetaLUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Skeleton
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.GramNondeg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.AgreeOnH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.LineReduce
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.WAniso

noncomputable section

namespace PI.UnitaryGroupMassFormula.BetaLUniq

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem betaLUniq_of_aniso_eigen (h3 : WAniso) (h5 : EigenvalueLastLineOne) : PI.BetaLUniq :=
  betaLUniq_of'' gram_matrix_nondegenerate agreeOnH h3 h5

end PI.UnitaryGroupMassFormula.BetaLUniq
