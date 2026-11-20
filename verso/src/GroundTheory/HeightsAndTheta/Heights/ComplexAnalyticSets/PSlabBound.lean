import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AffineOfCone
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
The claim follows from `GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SlabBound.affine`.
-/
theorem SlabBound.proof : SlabBound.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SlabBound.affine

end GroundTheory.Heights₂.Heights
