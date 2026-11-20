import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfProjectionAndFibreDim
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim | exact GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim | (intros; apply GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim <;> as …`.
-/
theorem _root_.GlobalTheory.T.generic_degree_of_projection_and_fibre_dim : PFCoordStatement → FibreDimStatement → GenDegStatement := by
  first | exact @GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim | exact GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim | (intros; apply GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim <;> assumption)
