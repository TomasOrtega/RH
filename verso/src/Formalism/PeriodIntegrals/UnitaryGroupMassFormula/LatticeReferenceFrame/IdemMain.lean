import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.IdemLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.IdemAd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.IdemTen

namespace PI.ScRefExists.Id

/- English proof (translation)
The claim follows from `idemLift_of_steps locIdem adOfLoc fixInt tenStep`.
-/
theorem idemLift : PI.ScRefExists.Sk.IdemLift :=
  idemLift_of_steps locIdem adOfLoc fixInt tenStep

end PI.ScRefExists.Id
