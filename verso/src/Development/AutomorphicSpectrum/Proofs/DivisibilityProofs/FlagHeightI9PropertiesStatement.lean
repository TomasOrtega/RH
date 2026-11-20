import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightI9Properties
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Top.flag_height_I9` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FFlagHeightI9Properties.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.flag_height_I9_properties : PB.FlagHeight → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ], 2 ≤ N → I9 (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.flag_height_I9 | exact GlobalTheory.CompanionTheory.Ar.Top.flag_height_I9 | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.flag_height_I9 <;> assumption)
