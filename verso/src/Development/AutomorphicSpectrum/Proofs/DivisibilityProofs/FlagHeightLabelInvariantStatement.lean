import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightLabelInvariant
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Top.hhFl_labelInv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FFlagHeightLabelInvariant.lean&line=129#L129)
-/
theorem _root_.GlobalTheory.T.flag_height_label_invariant : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ], 2 ≤ N → IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) → LabelInv (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.hhFl_labelInv | exact GlobalTheory.CompanionTheory.Ar.Top.hhFl_labelInv | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.hhFl_labelInv <;> assumption)
