import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.WeilBound.CoreStatements.IntegralPointHeights.NegativeIntegralPoints.FlDegFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FIntegralPointHeights%2FNegativeIntegralPoints%2FFlDegFree.lean&line=441#L441)
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_degree_polynomial_eval : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (lam : Wt Ψ N), 2 ≤ N → eval (fun x => lam x.1 x.2) (PB.degFlPoly Ψ N) = flagDeg lam := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IndefiniteRowSideFullHecke.degFlPoly_eval' | exact GlobalTheory.CompanionTheory.Ar.IndefiniteRowSideFullHecke.degFlPoly_eval'
