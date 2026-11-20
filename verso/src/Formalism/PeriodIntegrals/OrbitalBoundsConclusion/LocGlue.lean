import Formalism.PeriodIntegrals.LocHerm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.LocGlueOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocOProj

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem local_hermitian_glue : PI.LocHerm.LocGlue :=
  PI.LocHerm.Glue.locGlue_of projectiveOverOrder
