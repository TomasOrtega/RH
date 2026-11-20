import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

/- English proof (translation)
Introduce `_ _ _ _ _ _ hσ` and use `isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ)`.
-/
theorem smInfUnitary : SmInfUnitaryStatement :=
  fun _ _ _ _ _ _ hσ => isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ)

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
