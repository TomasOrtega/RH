import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsIntegralLogNormRat
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights.Inter

/- English proof (translation)
The claim follows from `PushforwardArithIntersection.proof arithVarZero hRat hCyc hInt`.
-/
theorem GenDeg.of_found (hRat : RatR.Statement) (hCyc : ArithmeticIntersectionCycle.Statement) (hInt : ArithmeticIntersectionIntegral.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.GenDegStatement :=
  PushforwardArithIntersection.proof arithVarZero hRat hCyc hInt

/- English proof (translation)
The claim follows from `GenDeg.of_found (RatR.proof hPts) hCyc (ArithmeticIntersectionIntegral.proof hPts hSec)`.
-/
theorem GenDeg.of_pts (hPts : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) (hSec : IntersectionWithSection.Statement)
    (hCyc : ArithmeticIntersectionCycle.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.GenDegStatement :=
  GenDeg.of_found (RatR.proof hPts) hCyc (ArithmeticIntersectionIntegral.proof hPts hSec)

end GroundTheory.Heights₂.Heights.Targets
