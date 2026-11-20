import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.HenselCountHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.MeasureEqOfCos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll

namespace PI.VolStabS

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem densV_of_gram (hF : GramFilt) : DensV :=
  densV_of_filt henselCount_holds cosDens_holds tensAll_holds hF

end PI.VolStabS
