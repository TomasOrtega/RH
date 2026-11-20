import Mathlib
import Formalism.PeriodIntegrals.ScalPairs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarEquivalenceGeneral.ScalarFactorEqOneOfLe

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem scalar_equiv_general : PI.ScalPairs.ScalarEquivG :=
  PI.UnitaryGroupMassFormula.ScalEquivGen.scalarEquivG_holds
