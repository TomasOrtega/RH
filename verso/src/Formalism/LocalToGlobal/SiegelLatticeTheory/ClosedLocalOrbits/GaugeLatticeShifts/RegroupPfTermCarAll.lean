import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfTermCar
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfRatIso
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfModGOfAt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfFrameCong

namespace Formalism.L2.SG.Pf.RegroupPf

/- English proof (translation)
The claim follows from `termCarC_of rational_isomorphism_holds reduction_mod_g_holds frame_congruence_holds`.
-/
theorem term_carrier_holds : TermCarC :=
  termCarC_of rational_isomorphism_holds reduction_mod_g_holds frame_congruence_holds

end Formalism.L2.SG.Pf.RegroupPf
