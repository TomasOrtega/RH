import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.FibreDim

namespace GlobalTheory.CompanionTheory.Ar.Giv

/- English proof (translation)
The claim follows from `GroundTheory.Heights₂.Heights.ForSecondHalf.FibreDim.proof`.
-/
theorem fibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement :=
  GroundTheory.Heights₂.Heights.ForSecondHalf.FibreDim.proof

end GlobalTheory.CompanionTheory.Ar.Giv
