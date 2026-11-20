import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVol
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensSAInt

namespace PI.VolStabSW

open VolAAW

/- English proof (translation)
The claim follows from `volAA_of (condAA_of (condExact_of sAf_holds hC))`.
-/
theorem volAA_of_chInf (hC : ChInf) : VolAA :=
  volAA_of (condAA_of (condExact_of sAf_holds hC))

/- English proof (translation)
The claim follows from `volAA_of_chInf (chInf_of_lift hL)`.
-/
theorem volAA_of_lift (hL : ChLift) : VolAA :=
  volAA_of_chInf (chInf_of_lift hL)

end PI.VolStabSW
