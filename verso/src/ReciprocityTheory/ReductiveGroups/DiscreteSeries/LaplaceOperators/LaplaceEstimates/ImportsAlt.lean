import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepDownStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepDown
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepUp

namespace ReciprocityTheory.ChartRestriction.DS.Lap

/- English proof (translation)
Introduce `hIS k r ε u h hg hp hq`. Conclude with `⟨stepDown hIS k r ε u h hg hp hq, stepUp hIS k r ε u h hg hp hq⟩`.
-/
theorem step : StepStatement := by
  intro hIS k r ε u h hg hp hq
  exact ⟨stepDown hIS k r ε u h hg hp hq, stepUp hIS k r ε u h hg hp hq⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
