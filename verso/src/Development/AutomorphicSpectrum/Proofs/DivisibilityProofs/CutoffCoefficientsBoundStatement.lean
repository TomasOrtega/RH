import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CutoffCoefficientsBound
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Top.flat_85_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FCutoffCoefficientsBound.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.cutoff_coefficients_bound : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) [Nonempty Ψ] (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C rd Lval : ℝ) (B₀ : ℕ) (A₀ b₀ : ℝ), T.Proportional → I9 (Ψ := Ψ) (N := N) hh → T.PropF II C rd Lval → 128 ≤ B₀ → T.bad.card ≤ B₀ → T.IdentAt II hh frob B₀ A₀ b₀ → |T.j * A₀ + N * b₀| ≤ C * N * bigLam B₀ rd Lval := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.flat_85_bound | exact GlobalTheory.CompanionTheory.Ar.Top.flat_85_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.flat_85_bound <;> assumption)
