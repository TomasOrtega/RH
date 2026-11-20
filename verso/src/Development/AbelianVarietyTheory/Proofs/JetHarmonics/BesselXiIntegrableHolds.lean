import Mathlib
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExistsOfIn
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable

namespace GlobalTheory

/- English proof (translation)
The claim follows from `ReciprocityTheory.ChartRestriction.DS.Xi.xiExists`.
-/
theorem besselXiIntegrable_holds : GlobalTheory.HCXi.BesselXiIntegrable :=
  ReciprocityTheory.ChartRestriction.DS.Xi.xiExists

end GlobalTheory
