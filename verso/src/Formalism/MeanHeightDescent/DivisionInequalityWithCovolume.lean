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
The claim follows from `log_covolume_slope_mu`.
-/
theorem lcvMu : LcvMu := log_covolume_slope_mu
/- English proof (translation)
The claim follows from `descent_slope`.
-/
theorem descentSlope : DescentSlope := descent_slope
/- English proof (translation)
The claim follows from `span_min_slope`.
-/
theorem spanMuMin : SpanMuMin := span_min_slope
/- English proof (translation)
The claim follows from `good_bad_split`.
-/
theorem goodBadCut : GoodBadCut := good_bad_split
/- English proof (translation)
The claim follows from `twist_lower_bound`.
-/
theorem twistLower : TwistLower := twist_lower_bound
/- English proof (translation)
The claim follows from `max_slope_minkowski`.
-/
theorem muMaxMinkowski : MuMaxMinkowski := max_slope_minkowski
/- English proof (translation)
The claim follows from `mean_height_sum_bound_holds`.
-/
theorem mean_height_sum_bound : CombinedAverageDegreeBound := mean_height_sum_bound_holds

end Formalism.ExtensionFiltration
