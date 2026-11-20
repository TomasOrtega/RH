import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVDx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVSec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.ExistsUnifFv

namespace PI.VolStabSW

/- English proof (translation)
The claim follows from `densV_of_gram (gramFilt_of (dxOpen_of secGram_holds))`.
-/
theorem densV_holds : DensV :=
  densV_of_gram (gramFilt_of (dxOpen_of secGram_holds))

end PI.VolStabSW
