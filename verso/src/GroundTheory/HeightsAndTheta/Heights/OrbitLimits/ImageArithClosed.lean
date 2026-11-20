import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageArith
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PBlockTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
The claim follows from `ImageArith.of_found BlockTrdeg.proof`.
-/
theorem imageArith : ReciprocityTheory.ChartRestriction.G.AI.I4.ImageArithStatement :=
  ImageArith.of_found BlockTrdeg.proof

end GroundTheory.Heights₂.Heights
