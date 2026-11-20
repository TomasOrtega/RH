import Mathlib
import Formalism.PeriodIntegrals.FinOrdAd
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdCpctDen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactTensorDensity.TensCpctDenOf

/- English proof (translation)
The claim follows from `PI.tensCpctDen_of compactBounded`.
-/
theorem tensor_compact_dense : PI.TensCpctDen := PI.tensCpctDen_of compactBounded
