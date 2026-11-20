import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LsLat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LSLocA

namespace PI.UnitaryGroupMassFormula.UJClassMass

/- English proof (translation)
The claim follows from `latStep_of_parts lsLat lsOne lsLoc`.
-/
theorem lattice_modification : LatStep := latStep_of_parts lsLat lsOne lsLoc

end PI.UnitaryGroupMassFormula.UJClassMass
