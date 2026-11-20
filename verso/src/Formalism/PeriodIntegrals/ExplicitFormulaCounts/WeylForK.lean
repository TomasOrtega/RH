import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylForK
import Formalism.PeriodIntegrals.ExplicitFormulaCounts.WeylForU

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem weylForK_closed : PI.WeylForK := weylForK_of weylForU_closed
