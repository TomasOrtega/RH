import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.IndexEqOfTraceInt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertPowD

noncomputable section

namespace PI

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem adelic_index_eq : PI.AdIndexEq.IndexEq :=
  PI.UnitaryGroupMassFormula.AdIndexEq.indexEq_of_traceInt PI.UnitaryGroupMassFormula.AdIndexEq.trace_integral'

end PI

end
