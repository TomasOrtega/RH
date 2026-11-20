import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.LieExponentialMajorantHolds

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

/- English proof (translation)
The claim follows from `LieExponentialMajorant.lieExponentialMajorant_holds`.
-/
theorem b5 : CayleyMajorantBound := LieExponentialMajorant.lieExponentialMajorant_holds

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
