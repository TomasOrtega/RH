import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightPowerSumOneZero
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Top.hhFl_pk_one_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FFlagHeightPowerSumOneZero.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.flag_height_power_sum_one_zero : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (τ : Ψ) (Q : RP Ψ N), 2 ≤ N → IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) → Q.IsHomogeneous (dimFl Ψ N) → hhFl Ψ N II (pk τ 1 * Q) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.hhFl_pk_one_mul | exact GlobalTheory.CompanionTheory.Ar.Top.hhFl_pk_one_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.hhFl_pk_one_mul <;> assumption)
