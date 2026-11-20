import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHVolLim

noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB Formalism.L2.SG.Pf.GE

/- English proof (translation)
The claim follows from `jacGauge_of_sandwich_gaugeMeasure hS VL.volLim hU hL`.
-/
theorem jacGauge_of_hearts3 (hS : Sandwich) (hU : ExistsGaugeMeasureForEachRank) (hL : RhsWLim) : JacGauge :=
  jacGauge_of_sandwich_gaugeMeasure hS VL.volLim hU hL

end Formalism.L2.SG.Pf
