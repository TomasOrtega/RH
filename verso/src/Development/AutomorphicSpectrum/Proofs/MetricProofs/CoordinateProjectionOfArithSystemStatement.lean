import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CoordinateProjectionOfArithSystem
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Relay.coordinate_projection_of_arith_system` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FCoordinateProjectionOfArithSystem.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.coordinate_projection_of_arith_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFCoordStatement := by
  first | exact @GlobalTheory.CompanionTheory.Relay.coordinate_projection_of_arith_system | exact GlobalTheory.CompanionTheory.Relay.coordinate_projection_of_arith_system | (intros; apply GlobalTheory.CompanionTheory.Relay.coordinate_projection_of_arith_system <;> assumption)
