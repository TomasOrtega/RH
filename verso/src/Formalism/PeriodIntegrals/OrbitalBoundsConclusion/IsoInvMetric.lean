import Mathlib
import Formalism.PeriodIntegrals.IsoInvMetric
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.IsoInvMetricOfHw
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.PolyEqZeroOfCircle

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isometry_invariant_metric : PI.IsoInvMetric.IsoInvMetric :=
  PI.IsoInvMetricW.isoInvMetric_of_hw PI.IsoInvMetricW.hermitian_weight
