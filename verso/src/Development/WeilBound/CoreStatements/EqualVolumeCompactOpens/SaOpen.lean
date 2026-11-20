import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Assembly

namespace PositivityTheory.EqVol

/- English proof (translation)
The claim follows from `GroundTheory.Heights₂.Heights.StrongApprox.SAHolds.full`.
-/
theorem sa : ReciprocityTheory.ChartRestriction.G.SA.SAStatement := GroundTheory.Heights₂.Heights.StrongApprox.SAHolds.full

/- English proof (translation)
The claim follows from `GroundTheory.Heights₂.Heights.StrongApprox.SAOpenHolds.full`.
-/
theorem saOpen : ReciprocityTheory.ChartRestriction.G.SA.SAOpenStatement := GroundTheory.Heights₂.Heights.StrongApprox.SAOpenHolds.full

end PositivityTheory.EqVol
