import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.OrbTupFin

namespace PI.VolStabS

/- English proof (translation)
The claim follows from `exStab_of_orb orbTup_holds hI hF hN`.
-/
theorem exStab_of_nu (hI : NuInv) (hF : NuFin) (hN : NuNeZero) : ExStab :=
  exStab_of_orb orbTup_holds hI hF hN

end PI.VolStabS
