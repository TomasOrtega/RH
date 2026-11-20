import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ImportsTer
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PFirstMinPos
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

/- English proof (translation)
Introduce `D` and use `FirstMinPos.proof D`.
-/
theorem UnitaryFirstMinimumPositive.proof : UnitaryFirstMinimumPositive.Statement :=
  fun D => FirstMinPos.proof D

end GroundTheory.Heights₂.Heights.NineStatements
