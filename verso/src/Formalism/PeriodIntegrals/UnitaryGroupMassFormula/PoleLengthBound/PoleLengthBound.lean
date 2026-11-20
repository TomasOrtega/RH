import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.StepsOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.BallQuot

namespace PI.PoleLengthCount

/- English proof (translation)
The claim follows from `pole_length_bound_of_balls pole_ballQuot`.
-/
theorem pole_length_bound : PI.LengthPoleInLift := pole_length_bound_of_balls pole_ballQuot

end PI.PoleLengthCount
