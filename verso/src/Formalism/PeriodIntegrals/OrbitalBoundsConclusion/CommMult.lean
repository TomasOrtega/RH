import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CommutingMultiplicity.CommMultOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CommutingMultiplicity.SchurStepAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CommutingMultiplicity.InjStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CommutingMultiplicity.IntegrableEntry

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem commutant_multiplicity_one : PI.UMultOne.CommutantMult :=
  PI.UnitaryGroupMassFormula.CommMult.commMult_of PI.UnitaryGroupMassFormula.CommMult.schurStep PI.UnitaryGroupMassFormula.CommMult.injStep PI.UnitaryGroupMassFormula.CommMult.avStep
