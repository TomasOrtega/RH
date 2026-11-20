import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharExGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleUnitsOpen.IsOpenAdicCompletionIntegers

/- English proof (translation)
The claim follows from `PI.IdeleUnitsOpenW.openUnits L`.
-/
theorem IdeleUnitsOpen (L : Type) [Field L] [NumberField L] : Formalism.L2.Host.CharEx.OpenUnits L :=
  PI.IdeleUnitsOpenW.openUnits L
