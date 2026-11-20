import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem LinesCoordImage.proof : LinesCoordImage.Statement := by
  intro K _ n m k B b c j
  funext l
  simp [coordProj, LinearMap.funLeft_apply, Module.Basis.equivFun_apply, Matrix.toBlocks₂₂,
    Module.Basis.toMatrix_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

end GroundTheory.Heights₂.Heights
