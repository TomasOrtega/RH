import Mathlib
import Formalism.PeriodIntegrals.UnitKron
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.PosDefFormNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.EqZeroOfMulVec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.IntRootProp

/- English proof (translation)
The claim follows from `PI.UnitKronW.unitKron_of PI.UnitKronW.stepA PI.UnitKronW.stepB PI.UnitKronW.stepC`.
-/
theorem unit_kronecker : PI.UnitKron :=
  PI.UnitKronW.unitKron_of PI.UnitKronW.stepA PI.UnitKronW.stepB PI.UnitKronW.stepC
