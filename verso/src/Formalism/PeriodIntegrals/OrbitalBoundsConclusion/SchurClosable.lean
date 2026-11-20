import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.SchurClosable
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurUnitaryInner.UnitaryInner

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.SchurClosable.Main.schurClosable`.
-/
theorem schur_closable : Formalism.IndefR.Leaf.SchurClosable :=
  PI.UnitaryGroupMassFormula.SchurClosable.Main.schurClosable
