import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BruhatHaarProved

noncomputable section

namespace Formalism.L2.SG.Pf

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem WB.rhsWLim' [Fact Formalism.L2.SG.Pf.WB.RhsWLim] : WB.RhsWLim := Fact.out

variable [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jacGauge : JacGauge := jacGauge_of_rhsW WB.rhsWLim'

end Formalism.L2.SG.Pf
