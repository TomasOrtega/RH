import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeKrullDimLe
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeFiniteFibreDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Introduce `n m h J hJ hm hmn hae` and use `hDim n m h J hJ hm hmn hae`.
-/
theorem ConeKrullDimLe.proof (hDim : ConeFiniteFibreDim.Statement) : ConeKrullDimLe.Statement :=
  fun n m h J hJ hm hmn hae => hDim n m h J hJ hm hmn hae

end GroundTheory.Heights₂.Heights
