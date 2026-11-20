import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphFactor
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSectionNormSqExtensionX
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

/- English proof (translation)
The claim follows from `LiftGraphFactor.proof GroundTheory.Heights₂.Heights.HilbertSamuel.SectionNormSqExtension.closed`.
-/
theorem LiftGraphFactor.closed : LiftGraphFactor.Statement :=
  LiftGraphFactor.proof GroundTheory.Heights₂.Heights.HilbertSamuel.SectionNormSqExtension.closed

end GroundTheory.Heights₂.Heights.Targets
