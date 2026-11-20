import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.MemOfProjEqZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.RieszRepresentationHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.ExistsIntegralMultiple

namespace PI.LocHerm.Glue

/- English proof (translation)
The claim follows from `locGlue_of_pair (pair_of rieszRepresentation_holds existsIntegralMultiple hO)`.
-/
theorem locGlue_of (hO : PI.LocHerm.LocOProj) : PI.LocHerm.LocGlue :=
  locGlue_of_pair (pair_of rieszRepresentation_holds existsIntegralMultiple hO)

end PI.LocHerm.Glue
