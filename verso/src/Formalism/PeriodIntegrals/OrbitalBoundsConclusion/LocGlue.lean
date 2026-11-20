import Formalism.PeriodIntegrals.LocHerm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.LocGlueOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocOProj

/- English proof (translation)
The claim follows from `PI.LocHerm.Glue.locGlue_of projectiveOverOrder`.
-/
theorem local_hermitian_glue : PI.LocHerm.LocGlue :=
  PI.LocHerm.Glue.locGlue_of projectiveOverOrder
