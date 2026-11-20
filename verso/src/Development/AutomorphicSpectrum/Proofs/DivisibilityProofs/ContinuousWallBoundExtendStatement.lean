import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ContinuousWallBoundExtend
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Top.rat_points_suffice_on_walls` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FContinuousWallBoundExtend.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.continuous_wall_bound_extend : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (c₀ b : ℝ) (τ₀ : Ψ) (Φ : Wt Ψ N → ℝ), 1 ≤ j → j < N → 0 < c₀ → Continuous Φ → (∀ lam, IsRatWt lam → InWall j τ₀ (c₀ / 2) lam → |Φ lam| ≤ b) → ∀ lam, InWall j τ₀ c₀ lam → |Φ lam| ≤ b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.rat_points_suffice_on_walls | exact GlobalTheory.CompanionTheory.Ar.Top.rat_points_suffice_on_walls | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.rat_points_suffice_on_walls <;> assumption)
