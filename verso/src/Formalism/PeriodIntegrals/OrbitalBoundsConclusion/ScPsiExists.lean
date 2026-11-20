import Mathlib
import Formalism.PeriodIntegrals.ScPsiExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sc_psi_exists : PI.ScPsiExists.Target :=
  PI.ScPsiExists.UnitaryGroupMassFormula.norm_units_of_calculation
