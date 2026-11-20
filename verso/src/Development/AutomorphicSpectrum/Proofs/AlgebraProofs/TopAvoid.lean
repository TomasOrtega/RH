import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Avoid

namespace GlobalTheory.CompanionTheory.Ar.Giv

/- English proof (translation)
The claim follows from `GroundTheory.Heights₂.Heights.ForSecondHalf.avoid`.
-/
theorem topAvoid : ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement :=
  GroundTheory.Heights₂.Heights.ForSecondHalf.avoid

end GlobalTheory.CompanionTheory.Ar.Giv
