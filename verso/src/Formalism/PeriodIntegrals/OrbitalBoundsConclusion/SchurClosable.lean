import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.SchurClosable
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurUnitaryInner.UnitaryInner

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem schur_closable : Formalism.IndefR.Leaf.SchurClosable :=
  PI.UnitaryGroupMassFormula.SchurClosable.Main.schurClosable
