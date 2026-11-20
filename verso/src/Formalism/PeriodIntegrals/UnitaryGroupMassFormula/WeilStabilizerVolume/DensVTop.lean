import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensVCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.HenselCountHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.MeasureEqOfCos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TensAll

namespace PI.VolStabW

/- English proof (translation)
The claim follows from `densV_of_filt henselCount_holds cosDens_holds tensAll_holds hF`.
-/
theorem densV_of_gram (hF : GramFilt) : DensV :=
  densV_of_filt henselCount_holds cosDens_holds tensAll_holds hF

end PI.VolStabW
