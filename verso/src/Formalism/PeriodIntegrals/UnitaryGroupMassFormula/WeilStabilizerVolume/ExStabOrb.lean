import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.ExStabFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.OrbTupFin

namespace PI.VolStabW

/- English proof (translation)
The claim follows from `exStab_of_orb orbTup_holds hI hF hN`.
-/
theorem exStab_of_nu (hI : NuInv) (hF : NuFin) (hN : NuNeZero) : ExStab :=
  exStab_of_orb orbTup_holds hI hF hN

end PI.VolStabW
