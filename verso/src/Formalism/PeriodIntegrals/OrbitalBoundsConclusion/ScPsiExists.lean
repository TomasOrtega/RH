import Mathlib
import Formalism.PeriodIntegrals.ScPsiExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation

/- English proof (translation)
The claim follows from `PI.ScPsiExists.UnitaryGroupMassFormula.norm_units_of_calculation`.
-/
theorem sc_psi_exists : PI.ScPsiExists.Target :=
  PI.ScPsiExists.UnitaryGroupMassFormula.norm_units_of_calculation
