import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfLeviAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfLeviWFin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfSratZ
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfLeviPos

namespace Formalism.L2.SG.Pf.SlabCount

/- English proof (translation)
The claim follows from `leviFinC_of (leviStabFinC_of (leviWFinC_of hP) rational_z_condition_holds)`.
-/
theorem leviFinC_of_pos (hP : LeviPosC) : LeviFinC :=
  leviFinC_of (leviStabFinC_of (leviWFinC_of hP) rational_z_condition_holds)

/- English proof (translation)
The claim follows from `leviFinC_of_pos levi_totally_positive_definite`.
-/
theorem levi_finite_index : LeviFinC :=
  leviFinC_of_pos levi_totally_positive_definite

end Formalism.L2.SG.Pf.SlabCount
