import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvOA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvF

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rhsWInv_of_hypQ (hQ : HypQ) : RhsWInv := rhsWInv_of_hyp hQ unimodK fibTrans

end PI.RhsWLim.W.RI
