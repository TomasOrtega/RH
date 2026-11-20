import Mathlib
import Formalism.PeriodIntegrals.HookBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.NablaGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.NablaOperatorBasis

/- English proof (translation)
The claim follows from `PI.SlopeSteps.stdSlopeLow_of PI.SlopeSteps.nabla_gram_lower_bound PI.SlopeSteps.gram_matrix_duality PI.SlopeSteps.nabla_operator_basis`.
-/
theorem standard_slope_lower : PI.StdSlopeLow :=
  PI.SlopeSteps.stdSlopeLow_of PI.SlopeSteps.nabla_gram_lower_bound PI.SlopeSteps.gram_matrix_duality
    PI.SlopeSteps.nabla_operator_basis
