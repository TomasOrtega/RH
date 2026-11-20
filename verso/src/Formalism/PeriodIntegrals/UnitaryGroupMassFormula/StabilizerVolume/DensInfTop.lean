import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfCV

noncomputable section

namespace PI.VolStabS

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem submLocal_holds : SubmLocal := submLocal_of linDens_holds changeVar_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem submDens_holds : SubmDens := submDens_of_local submLocal_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem densInf_of_coord (h : CoordInf) : DensInf := densInf_of submDens_holds h

end PI.VolStabS
