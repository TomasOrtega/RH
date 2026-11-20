import Mathlib
import Formalism.PeriodIntegrals.ScMuExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.TargetOfInstDecomp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstAll

namespace PI

/- English proof (translation)
The claim follows from `PI.ScMuExists.UnitaryGroupMassFormula.target_of_instDecomp PI.ScMuExists.UnitaryGroupMassFormula.place_decomposition_instance`.
-/
theorem sc_mu_exists : PI.ScMuExists.Target :=
  PI.ScMuExists.UnitaryGroupMassFormula.target_of_instDecomp PI.ScMuExists.UnitaryGroupMassFormula.place_decomposition_instance

end PI
