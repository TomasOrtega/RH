import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFT
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFIn

namespace PI.VolStabSW

/- English proof (translation)
The claim follows from `fFCount_of_inert FFHS.fFInert_holds`.
-/
theorem fFCount_holds : FFCount := fFCount_of_inert FFHS.fFInert_holds

end PI.VolStabSW
