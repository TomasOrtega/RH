import Formalism.PeriodIntegrals.LengthPoleInLift
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PoleLengthBound

/- English proof (translation)
The claim follows from `PI.PoleLengthCount.pole_length_bound`.
-/
theorem length_pole_t0 : PI.LengthPoleInLift := PI.PoleLengthCount.pole_length_bound
