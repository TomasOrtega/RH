import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensChLift

namespace PI.VolStabSW

/- English proof (translation)
The claim follows from `volAA_of_lift chLift_holds`.
-/
theorem volAA_holds : VolAA := volAA_of_lift chLift_holds

end PI.VolStabSW
