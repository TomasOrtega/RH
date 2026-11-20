import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensFFT
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensFFIn

namespace PI.VolStabW

/- English proof (translation)
The claim follows from `fFCount_of_inert FFHS.fFInert_holds`.
-/
theorem fFCount_holds : FFCount := fFCount_of_inert FFHS.fFInert_holds

end PI.VolStabW
