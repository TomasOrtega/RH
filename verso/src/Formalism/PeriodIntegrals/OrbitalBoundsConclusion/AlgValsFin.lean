import Mathlib
import Formalism.PeriodIntegrals.AlgValsFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem algebraic_values_finite (L : Type) [Field L] [NumberField L] : PI.AlgValsFin.AlgValsFin L :=
  PI.AlgValsFin.W.algValsFin_main L

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem algValsFin (L : Type) [Field L] [NumberField L] : PI.AlgValsFin.AlgValsFin L :=
  algebraic_values_finite L
