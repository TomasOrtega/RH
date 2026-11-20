import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.AigGen
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `PositivityTheory.HtPt.Aig.genDeg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FHodgeTatePoints%2FAigGen.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim : PFCoordStatement → FibreDimStatement → GenDegStatement := by
  first | exact @PositivityTheory.HtPt.Aig.genDeg | exact PositivityTheory.HtPt.Aig.genDeg
