import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem smInfUnitary : SmInfUnitaryStatement :=
  fun _ _ _ _ _ _ hσ => isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ)

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
