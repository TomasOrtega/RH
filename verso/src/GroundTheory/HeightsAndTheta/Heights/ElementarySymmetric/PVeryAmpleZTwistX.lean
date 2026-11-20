import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZTwist
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem VeryAmpleZTwist.proof_closed : VeryAmpleZTwist.Statement.{u, v, w} :=
  VeryAmpleZTwist.proof VeryAmpleZFamily.proof

end GroundTheory.Heights₂.Heights.Kleiman
