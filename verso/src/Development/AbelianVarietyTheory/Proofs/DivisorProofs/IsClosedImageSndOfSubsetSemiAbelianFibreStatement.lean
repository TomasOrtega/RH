import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSndOfSubsetSemiAbelianFibre
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsClosedImageSndOfSubsetSemiAbelianFibre.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.isClosed_image_snd_of_subset_semiAbelian_fibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) → ∀ N : Set (G ⊗ G).left, IsClosed N → N ⊆ (fst G G).left ⁻¹' {x} → IsClosed ((snd G G).left '' N) := by
  first | exact @GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint | exact GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint | (intros; apply GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint <;> assumption)
