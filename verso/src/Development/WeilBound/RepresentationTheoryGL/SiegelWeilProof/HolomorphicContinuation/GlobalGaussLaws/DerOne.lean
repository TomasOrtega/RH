import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOneB
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOneC

namespace PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
The claim follows from `derivOne_of h curveSt`.
-/
theorem derivOne (h : GlobalTheory.Published.WeilThetaConvergence) : DerivOne := derivOne_of h curveSt

end PositivityTheory.Rg.Sw.Glob
