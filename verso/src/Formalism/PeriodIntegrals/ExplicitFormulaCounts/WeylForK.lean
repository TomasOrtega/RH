import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylForK
import Formalism.PeriodIntegrals.ExplicitFormulaCounts.WeylForU

/- English proof (translation)
The claim follows from `weylForK_of weylForU_closed`.
-/
theorem weylForK_closed : PI.WeylForK := weylForK_of weylForU_closed
