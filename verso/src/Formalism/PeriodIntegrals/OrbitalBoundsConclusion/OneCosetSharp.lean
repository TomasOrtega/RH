import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.OneCosetSharpOfPatClosed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.KappaZeroAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.AllowColLt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.EntryEmbedMatrix

/- English proof (translation)
The claim follows from `PI.OneCosetSharp.W.oneCosetSharp_of_patClosed PI.OneCosetSharp.W.patClosed PI.OneCosetSharp.W.kappaZero PI.OneCosetSharp.W.nElem PI.OneCosetSharp.W.gaStep PI.OneCosetSharp.W.C2.claim2`.
-/
theorem support_oneCoset : PI.OneCosetSharp.OneCosetSharp :=
  PI.OneCosetSharp.W.oneCosetSharp_of_patClosed PI.OneCosetSharp.W.patClosed PI.OneCosetSharp.W.kappaZero
    PI.OneCosetSharp.W.nElem PI.OneCosetSharp.W.gaStep PI.OneCosetSharp.W.C2.claim2
