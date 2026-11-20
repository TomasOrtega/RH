import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericFreeness
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericNoetherNormalisation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v w

/- English proof (translation)
The claim follows from `GenericFreeness.proof GenericNoetherNormalisation.proof`.
-/
theorem GenericFreeness.full : GenericFreeness.Statement.{u, v, w} :=
  GenericFreeness.proof GenericNoetherNormalisation.proof

end GroundTheory.Heights₂.Heights
