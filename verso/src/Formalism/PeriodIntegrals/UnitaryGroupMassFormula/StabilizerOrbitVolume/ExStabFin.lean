import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.ExStabU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoClose

noncomputable section

namespace PI.VolStabSW

/- English proof (translation)
The claim follows from `exStab_of_U secCtblW_holds lcscPolish_holds hO hI hF hN`.
-/
theorem exStab_of_orb (hO : OrbTup) (hI : NuInv) (hF : NuFin) (hN : NuNeZero) : ExStab :=
  exStab_of_U secCtblW_holds lcscPolish_holds hO hI hF hN

end PI.VolStabSW
