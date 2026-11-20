import Formalism.MeanHeightDescent.AverageDegreeBounds.Assembly
import Formalism.MeanHeightDescent.AverageDegreeBounds.DescentCut
import Formalism.MeanHeightDescent.AverageDegreeBounds.DescentSlope
import Mathlib
import Formalism.MeanHeightDescent.StatementJ
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq
import Formalism.MeanHeightDescent.AverageDegreeBounds.CovolumeFullAssemblyHolds
import Formalism.MeanHeightDescent.AverageDegreeBounds.GoodBadCut
import Formalism.MeanHeightDescent.AverageDegreeBounds.CovolumeAssemblyHolds
import Formalism.MeanHeightDescent.AverageDegreeBounds.MuMaxMinkowski
import Formalism.MeanHeightDescent.AverageDegreeBounds.CovolumeIntoDivisionHolds
import Formalism.MeanHeightDescent.AverageDegreeBounds.CombinedAverageDegreeBoundOf
import Formalism.MeanHeightDescent.FlatDefect
import Formalism.MeanHeightDescent.AverageDegreeBounds.SpanMuMin
import Formalism.MeanHeightDescent.AverageDegreeBounds.SumComponents
import Formalism.MeanHeightDescent.AverageDegreeBounds.TwistLower

namespace Formalism.ExtensionFiltration

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lcvMu : LcvMu := log_covolume_slope_mu
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem descentSlope : DescentSlope := descent_slope
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem spanMuMin : SpanMuMin := span_min_slope
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem goodBadCut : GoodBadCut := good_bad_split
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem twistLower : TwistLower := twist_lower_bound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem muMaxMinkowski : MuMaxMinkowski := max_slope_minkowski
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mean_height_sum_bound : CombinedAverageDegreeBound := mean_height_sum_bound_holds

end Formalism.ExtensionFiltration
