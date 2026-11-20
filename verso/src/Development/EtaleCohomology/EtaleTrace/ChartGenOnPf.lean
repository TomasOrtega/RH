import Development.EtaleCohomology.EtaleTrace.ChartGenOnPfCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial

namespace LateralTheory.EtaleTrace.Cov

/- English proof (translation)
The claim follows from `ChartGenOn_of ChartGenMem_pf h`.
-/
theorem ChartGenOn_of_val (h : ChartGenVal) : ChartGenOn := ChartGenOn_of ChartGenMem_pf h

end LateralTheory.EtaleTrace.Cov
