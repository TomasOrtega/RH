import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.LetterSize
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZIterC

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

namespace PI.UnitaryGroupMassFormula.UsCost

/- English proof (translation)
The claim follows from `zeta_cost_of_smooth_deriv hS hD hDS`.
-/
theorem zCost_of (hS : ZSmooth) (hD : ZDeriv) (hDS : DirSize) : ZCost :=
  zeta_cost_of_smooth_deriv hS hD hDS

end PI.UnitaryGroupMassFormula.UsCost
