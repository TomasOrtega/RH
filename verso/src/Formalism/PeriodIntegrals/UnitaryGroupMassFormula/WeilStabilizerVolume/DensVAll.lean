import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensVTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensVDx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensVSec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.ExistsUnifFv

namespace PI.VolStabW

/- English proof (translation)
The claim follows from `densV_of_gram (gramFilt_of (dxOpen_of secGram_holds))`.
-/
theorem densV_holds : DensV :=
  densV_of_gram (gramFilt_of (dxOpen_of secGram_holds))

end PI.VolStabW
