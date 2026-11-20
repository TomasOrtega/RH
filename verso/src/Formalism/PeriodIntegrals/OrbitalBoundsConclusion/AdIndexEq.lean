import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.IndexEqOfTraceInt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertPowD

noncomputable section

namespace PI

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.AdIndexEq.indexEq_of_traceInt PI.UnitaryGroupMassFormula.AdIndexEq.trace_integral'`.
-/
theorem adelic_index_eq : PI.AdIndexEq.IndexEq :=
  PI.UnitaryGroupMassFormula.AdIndexEq.indexEq_of_traceInt PI.UnitaryGroupMassFormula.AdIndexEq.trace_integral'

end PI

end
