import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.IsCompactUnitaryMat

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

/- English proof (translation)
Introduce `k r` and use `StandardBasisEmbedding.main k r`.
-/
theorem b7a : ExistsUnitaryHaarProbability := fun k r => StandardBasisEmbedding.main k r

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
