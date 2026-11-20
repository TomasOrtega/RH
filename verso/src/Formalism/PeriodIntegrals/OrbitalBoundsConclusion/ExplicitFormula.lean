import Mathlib
import Formalism.PeriodIntegrals.ExplicitFormula
import Formalism.PeriodIntegrals.ZerosWindow
import Formalism.PeriodIntegrals.ZerosWindowIn
import Formalism.PeriodIntegrals.DiscIn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LocalLemmaOfHelpers

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem explicitFormula_of : PI.ZerosWindow → PI.DiscFactor → PI.DiscLog → PI.LBoundRight →
    PI.ZetaBoundRight → PI.LInvRight → PI.ExplicitFormula :=
  PI.EF.explicitFormula_main
