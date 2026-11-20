import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.PfCoordOfSystem
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `PositivityTheory.HtPt.Aig.pfCoord` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FHodgeTatePoints%2FPfCoordOfSystem.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.coordinate_projection_of_arith_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFCoordStatement := by
  first | exact @PositivityTheory.HtPt.Aig.pfCoord | exact PositivityTheory.HtPt.Aig.pfCoord
