import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeKrullDimLe
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeFiniteFibreDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem ConeKrullDimLe.proof (hDim : ConeFiniteFibreDim.Statement) : ConeKrullDimLe.Statement :=
  fun n m h J hJ hm hmn hae => hDim n m h J hJ hm hmn hae

end GroundTheory.Heights₂.Heights
