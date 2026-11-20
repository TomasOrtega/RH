import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BridgeRA

noncomputable section

namespace Formalism.L2.SG.Pf

/- English proof (translation)
The claim follows from `iotaDictAllC_of iotaBridgeRAC_holds`.
-/
theorem iotaDictAllC_holds : IotaDictAllC := iotaDictAllC_of iotaBridgeRAC_holds

/- English proof (translation)
The claim follows from `iotaDictC_holds_of iotaBridgeRAC_holds`.
-/
theorem iotaDictC_holds : IotaDictC := iotaDictC_holds_of iotaBridgeRAC_holds

end Formalism.L2.SG.Pf
