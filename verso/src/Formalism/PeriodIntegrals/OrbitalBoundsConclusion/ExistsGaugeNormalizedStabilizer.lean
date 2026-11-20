import Mathlib
import Formalism.PeriodIntegrals.ExistsGaugeMeasureForEachRank
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CircleGaugeAction.ContinuousLmulM

/- English proof (translation)
Introduce `r` and use `⟨PI.ExistsGaugeMeasureForEachRank.W.μG r, PI.ExistsGaugeMeasureForEachRank.W.gauge r⟩`.
-/
theorem exists_gaugeNormalizedStabilizer : PI.ExistsGaugeMeasureForEachRank.ExistsGaugeMeasureForEachRank := fun r => ⟨PI.ExistsGaugeMeasureForEachRank.W.μG r, PI.ExistsGaugeMeasureForEachRank.W.gauge r⟩
