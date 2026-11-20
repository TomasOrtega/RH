import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerConvI2
import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FRealTowerConvI2.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.real_tower_conv_I2 : PB.AgreementPos → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), T.Conv II ∧ T.I2 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.real_tower_convergence_I2 | exact GlobalTheory.CompanionTheory.Ar.Top.real_tower_convergence_I2 | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.real_tower_convergence_I2 <;> assumption)
