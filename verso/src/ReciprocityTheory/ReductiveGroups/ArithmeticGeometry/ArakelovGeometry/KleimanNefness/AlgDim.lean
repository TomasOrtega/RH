import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDimSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDimA

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

/- English proof (translation)
The claim follows from `KrullDimensionPrincipalIdeal.dimPIT'`.
-/
theorem dimPIT : DimPITStatement := KrullDimensionPrincipalIdeal.dimPIT'

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
