import Mathlib
import Formalism.PeriodIntegrals.LocHerm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalOrderProjection.LocOProjOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalOrderProjection.ProjOfFreeIdem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalOrderProjection.IsFieldOfNonsq

/- English proof (translation)
The claim follows from `PI.LocHerm.OProj.locOProj_of PI.LocHerm.OProj.sqCase PI.LocHerm.OProj.nonSqCase`.
-/
theorem projectiveOverOrder : PI.LocHerm.LocOProj :=
  PI.LocHerm.OProj.locOProj_of PI.LocHerm.OProj.sqCase PI.LocHerm.OProj.nonSqCase
