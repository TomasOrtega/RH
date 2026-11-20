import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfProjectionAndFibreDim
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FGenericDegreeOfProjectionAndFibreDim.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.generic_degree_of_projection_and_fibre_dim : PFCoordStatement → FibreDimStatement → GenDegStatement := by
  first | exact @GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim | exact GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim | (intros; apply GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim <;> assumption)
