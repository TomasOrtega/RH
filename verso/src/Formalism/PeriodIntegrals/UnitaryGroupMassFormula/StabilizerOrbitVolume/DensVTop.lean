import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.HenselCountHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.MeasureEqOfCos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll

namespace PI.VolStabSW

/- English proof (translation)
The claim follows from `densV_of_filt henselCount_holds cosDens_holds tensAll_holds hF`.
-/
theorem densV_of_gram (hF : GramFilt) : DensV :=
  densV_of_filt henselCount_holds cosDens_holds tensAll_holds hF

end PI.VolStabSW
