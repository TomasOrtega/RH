import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussM
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousGramX
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.HermTranspose
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GWickC

namespace PositivityTheory.Rg.Sw.WR.G

/- English proof (translation)
The claim follows from `gauss_of integP (wick_of integP) rot base`.
-/
theorem gauss : Gauss := gauss_of integP (wick_of integP) rot base

end PositivityTheory.Rg.Sw.WR.G
