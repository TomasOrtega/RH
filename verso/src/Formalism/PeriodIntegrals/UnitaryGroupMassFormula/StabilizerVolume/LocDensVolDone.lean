import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensChLift

namespace PI.VolStabS

/- English proof (translation)
The claim follows from `volAA_of_lift chLift_holds`.
-/
theorem volAA_holds : VolAA := volAA_of_lift chLift_holds

end PI.VolStabS
