import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensInfCV

noncomputable section

namespace PI.VolStabW

/- English proof (translation)
The claim follows from `submLocal_of linDens_holds changeVar_holds`.
-/
theorem submLocal_holds : SubmLocal := submLocal_of linDens_holds changeVar_holds

/- English proof (translation)
The claim follows from `submDens_of_local submLocal_holds`.
-/
theorem submDens_holds : SubmDens := submDens_of_local submLocal_holds

/- English proof (translation)
The claim follows from `densInf_of submDens_holds h`.
-/
theorem densInf_of_coord (h : CoordInf) : DensInf := densInf_of submDens_holds h

end PI.VolStabW
