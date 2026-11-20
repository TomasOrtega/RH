import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.HasDerivAtDet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

/- English proof (translation)
The claim follows from `LogDetDerivative.intersectionNumber_baseChange`.
-/
theorem LogDetDerivative.proof : LogDetDerivative.Statement :=
  LogDetDerivative.intersectionNumber_baseChange

end GroundTheory.Heights₂.Heights.HilbertSamuel
