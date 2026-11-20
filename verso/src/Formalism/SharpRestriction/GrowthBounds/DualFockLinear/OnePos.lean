import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RowGenCoeffZero
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.ThetaInjHd

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem onePos_of_opBound (hOB : OpBound) (hT : RestTheta) (hW : RestWt) : OnePos :=
  onePos_of hOB restAdj restStab hT hW restRep restRep2

end Formalism.MainNotions.TestSideCounting
