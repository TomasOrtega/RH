import Mathlib
import Formalism.PeriodIntegrals.BetaLUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.BetaLUniqOfAnisoEigen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.EigenvalueLastLineOne

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.BetaLUniq.betaLUniq_of_aniso_eigen PI.UnitaryGroupMassFormula.BetaLUniq.weight_space_anisotropic PI.UnitaryGroupMassFormula.BetaLUniq.eigenvalue_last_line_eq_one`.
-/
theorem beta_l_unique : PI.BetaLUniq :=
  PI.UnitaryGroupMassFormula.BetaLUniq.betaLUniq_of_aniso_eigen PI.UnitaryGroupMassFormula.BetaLUniq.weight_space_anisotropic
    PI.UnitaryGroupMassFormula.BetaLUniq.eigenvalue_last_line_eq_one
