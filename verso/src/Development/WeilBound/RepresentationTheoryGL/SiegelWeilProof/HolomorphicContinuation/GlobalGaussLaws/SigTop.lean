import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SigOKOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WittLt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WittEq

namespace PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
The claim follows from `sigOK_of wittLBlt wittLBeq`.
-/
theorem sigOK : SigOK := sigOK_of wittLBlt wittLBeq

end PositivityTheory.Rg.Sw.Glob
