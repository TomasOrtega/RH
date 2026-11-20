import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsSingleBlockSegre
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FCoordsSingleBlockSegre.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.coords_single_block_segre : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω), CoordTie ℤ ξ x → CoordTie ℤ ξ (fun c' : (k : Unit) → (fun _ : Unit => Fin (N + 1)) k => ∏ k, (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) ⟨k, c' k⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Reindex.coordTie_one_block | exact GlobalTheory.CompanionTheory.Ar.SncBase.Reindex.coordTie_one_block | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Reindex.coordTie_one_block <;> assumption)
