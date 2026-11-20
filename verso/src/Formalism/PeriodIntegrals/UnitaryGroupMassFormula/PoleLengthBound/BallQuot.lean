import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiBallFromAlt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BallQuotLen

noncomputable section

namespace PI.PoleLengthCount

/- English proof (translation)
The claim follows from `ball_quotient_length`.
-/
theorem pole_ballQuot : BallQuot := ball_quotient_length

end PI.PoleLengthCount
