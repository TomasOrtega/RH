import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IntersectionSystemDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FIntersectionSystemDegree.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.intersection_system_degree : ∀ II : IntersectionSystem, IsIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.degreeStatement_of_intersectionSystem | exact GlobalTheory.CompanionTheory.Ar.Top.degreeStatement_of_intersectionSystem | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.degreeStatement_of_intersectionSystem <;> assumption)
