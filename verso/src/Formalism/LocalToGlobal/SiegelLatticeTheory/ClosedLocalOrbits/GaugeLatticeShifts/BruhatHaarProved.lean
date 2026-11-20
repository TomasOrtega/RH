import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacGaugeOfSandwichRhsWLim
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstSandwich

noncomputable section

namespace Formalism.L2.SG.Pf

/- English proof (translation)
The claim follows from `jacGauge_of_sandwich_rhsWLim BH.sandwich' hL`.
-/
theorem jacGauge_of_rhsW (hL : WB.RhsWLim) : JacGauge := jacGauge_of_sandwich_rhsWLim BH.sandwich' hL

end Formalism.L2.SG.Pf
