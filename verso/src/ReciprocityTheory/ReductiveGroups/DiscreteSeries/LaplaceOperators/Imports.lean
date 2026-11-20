import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ParitySignEqGapSign
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.StepIBase
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ImportsAlt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.DecDeriv

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

/- English proof (translation)
The claim follows from `nv_of Base.stepIBase step hIS S0.DecDeriv.decDeriv`.
-/
theorem nv (hIS : S0.IntSStatement) : NVStatement :=
  nv_of Base.stepIBase step hIS S0.DecDeriv.decDeriv

end ReciprocityTheory.ChartRestriction.DS.Lap
