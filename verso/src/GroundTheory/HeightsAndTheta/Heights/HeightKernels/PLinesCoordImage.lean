import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

/- English proof (translation)
Introduce `K _ n m k B b c j`. Use function extensionality and compare the values at `l`. Simplify using `[coordProj, LinearMap.funLeft_apply, Module.Basis.equivFun_apply, Matrix.toBlocks₂₂, Module.Basis.toMatrix_apply, Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem LinesCoordImage.proof : LinesCoordImage.Statement := by
  intro K _ n m k B b c j
  funext l
  simp [coordProj, LinearMap.funLeft_apply, Module.Basis.equivFun_apply, Matrix.toBlocks₂₂,
    Module.Basis.toMatrix_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

end GroundTheory.Heights₂.Heights
