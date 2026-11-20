import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.BesselVectors.BesselNVGOfNv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Imports
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.FamilyGapImplicationHolds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.NVHTop

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TopClosed

/- English proof (translation)
The claim follows from `nv NVHTop.intS`.
-/
theorem nvAll : NVStatement := nv NVHTop.intS

/- English proof (translation)
The claim follows from `TopFinal.besselNVG_of_nv nvAll`.
-/
theorem besselNVG : TopNV.BesselNVG := TopFinal.besselNVG_of_nv nvAll

end ReciprocityTheory.ChartRestriction.DS.Lap.TopClosed
