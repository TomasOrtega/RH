import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TailInt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.PolynomialGrowthIntegrals
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.SlowWeightBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.PlanarKernelBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.OscillatoryBound

namespace ReciprocityTheory.ChartRestriction.DS.Xi

/- English proof (translation)
The claim follows from `quadraticSublevelDecay'`.
-/
theorem sub : SUB := quadraticSublevelDecay'

/- English proof (translation)
The claim follows from `planarKernelBound'`.
-/
theorem ker : KER := planarKernelBound'

/- English proof (translation)
The claim follows from `slowWeightBound'`.
-/
theorem slow : SLOW := slowWeightBound'

end ReciprocityTheory.ChartRestriction.DS.Xi
