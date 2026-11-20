import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerI1
import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Top.TowerOverReals.tower_I1_of_reference_linked` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FRealTowerI1.lean&line=79#L79)
-/
theorem _root_.GlobalTheory.T.real_tower_I1 : PB.Coefficients → PB.AgreementPos → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), R.RefLinked II → T.I1 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.TowerOverReals.tower_I1_of_reference_linked | exact GlobalTheory.CompanionTheory.Ar.Top.TowerOverReals.tower_I1_of_reference_linked | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.TowerOverReals.tower_I1_of_reference_linked <;> assumption)
