import Mathlib
import Formalism.PeriodIntegrals.ScalPairs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarEquivalenceGeneral.ScalarFactorEqOneOfLe

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.ScalEquivGen.scalarEquivG_holds`.
-/
theorem scalar_equiv_general : PI.ScalPairs.ScalarEquivG :=
  PI.UnitaryGroupMassFormula.ScalEquivGen.scalarEquivG_holds
