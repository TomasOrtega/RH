import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerI3OfSemipositiveNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Top.RootTower.tower_I3_of_nef_inputs` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FTowerI3OfSemipositiveNef.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.tower_I3_of_semipositive_nef : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.A1 → T.ModelNefStatement → T.M2 → T.ANef → T.I3 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.RootTower.tower_I3_of_nef_inputs | exact GlobalTheory.CompanionTheory.Ar.Top.RootTower.tower_I3_of_nef_inputs | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.RootTower.tower_I3_of_nef_inputs <;> assumption)
