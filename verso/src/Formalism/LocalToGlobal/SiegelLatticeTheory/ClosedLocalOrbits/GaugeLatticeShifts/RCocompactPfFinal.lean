import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMain
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfApproxFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMem

namespace Formalism.L2.SG.TermOp.Vanish

/- English proof (translation)
The claim follows from `rCocompactC_of ratApprox_holds ratMem_holds`.
-/
theorem rational_cocompact_holds : RCocompactC := rCocompactC_of ratApprox_holds ratMem_holds

end Formalism.L2.SG.TermOp.Vanish
