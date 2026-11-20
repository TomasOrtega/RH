import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BruhatHaarProved

noncomputable section

namespace Formalism.L2.SG.Pf

/- English proof (translation)
The claim follows from `Fact.out`.
-/
theorem WB.rhsWLim' [Fact Formalism.L2.SG.Pf.WB.RhsWLim] : WB.RhsWLim := Fact.out

variable [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in

/- English proof (translation)
The claim follows from `jacGauge_of_rhsW WB.rhsWLim'`.
-/
theorem jacGauge : JacGauge := jacGauge_of_rhsW WB.rhsWLim'

end Formalism.L2.SG.Pf
