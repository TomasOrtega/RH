import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.CongruenceLiftOfBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IdxTop

namespace PI.LocMassTypL

open PI.LocMassTypW

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem index_formula_of_split (hS : SplitR) (hU : KUnip1) : StepIdx :=
  index_formula_of_lift (congruence_lift_of_split hS) hU

end PI.LocMassTypL
