import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerT
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerN
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerM
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CycSecM

namespace PositivityTheory.Rg.Sw.AbsSt

/- English proof (translation)
The claim follows from `secDer_of nDer mDer`.
-/
theorem secDer : SecDer := secDer_of nDer mDer

end PositivityTheory.Rg.Sw.AbsSt
