import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.ExStabFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.OrbTupFin

namespace PI.VolStabW

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exStab_of_nu (hI : NuInv) (hF : NuFin) (hN : NuNeZero) : ExStab :=
  exStab_of_orb orbTup_holds hI hF hN

end PI.VolStabW
