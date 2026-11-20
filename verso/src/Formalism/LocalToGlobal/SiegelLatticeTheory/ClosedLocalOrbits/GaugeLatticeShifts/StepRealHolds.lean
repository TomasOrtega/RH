import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem StepReal_holds : StepReal :=
  stepReal_of_witt (fun _ _ ε x y hG hnd => Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.witt_of_gram ε x y hG hnd)

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
