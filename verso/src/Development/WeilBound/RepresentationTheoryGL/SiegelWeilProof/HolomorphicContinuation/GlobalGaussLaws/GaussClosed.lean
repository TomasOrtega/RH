import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussFinal
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FTfact
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellA

namespace PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
The claim follows from `gaussian_law_of_weil wEx fTfact`.
-/
theorem gaussLaw : GaussLaw := gaussian_law_of_weil wEx fTfact

end PositivityTheory.Rg.Sw.Glob
