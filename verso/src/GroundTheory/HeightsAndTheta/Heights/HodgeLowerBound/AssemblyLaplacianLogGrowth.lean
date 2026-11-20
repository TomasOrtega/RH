import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PLaplacianLogGrowth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFsPotLaplacian
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PInvDerivDecay
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PLaplacianDecayZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

/- English proof (translation)
The claim follows from `LaplacianLogGrowth.proof FsPotLaplacian.proof InvDerivDecay.proof LaplacianDecayZero.proof`.
-/
theorem LaplacianLogGrowth.full : LaplacianLogGrowth.Statement :=
  LaplacianLogGrowth.proof FsPotLaplacian.proof InvDerivDecay.proof LaplacianDecayZero.proof

end GroundTheory.Heights₂.Heights.LowerBoundFree
