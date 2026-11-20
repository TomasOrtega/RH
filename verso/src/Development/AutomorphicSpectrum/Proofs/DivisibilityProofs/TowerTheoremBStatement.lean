import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerTheoremB
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Top.thmB_functional` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FTowerTheoremB.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.tower_theorem_B : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.Proportional → T.ThmW II → T.I8 II hh → I9 (Ψ := Ψ) (N := N) hh → T.ThmB II hh := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.thmB_functional | exact GlobalTheory.CompanionTheory.Ar.Top.thmB_functional | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.thmB_functional <;> assumption)
