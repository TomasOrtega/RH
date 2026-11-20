import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PVectorOrbitsFinite
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerExtra

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LineIndexNeZero.proof (E W : Type*) [Field E] [NumberField E] [AddCommGroup W]
    [Module E W] : LineIndexNeZero.Statement E W :=
  _root_.UpperTheory.Reformulated.B.Gub1.proof E W

end GroundTheory.Heights₂.Heights.FiniteCovolume
