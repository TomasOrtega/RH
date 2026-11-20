import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVDx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVSec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.ExistsUnifFv

namespace PI.VolStabSW

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem densV_holds : DensV :=
  densV_of_gram (gramFilt_of (dxOpen_of secGram_holds))

end PI.VolStabSW
