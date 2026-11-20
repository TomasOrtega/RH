import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepDownStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepDown
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepUp

namespace ReciprocityTheory.ChartRestriction.DS.Lap

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem step : StepStatement := by
  intro hIS k r ε u h hg hp hq
  exact ⟨stepDown hIS k r ε u h hg hp hq, stepUp hIS k r ε u h hg hp hq⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
