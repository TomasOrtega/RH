import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueCentreLocalHom
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.exists_unique_point_of_local` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FExistsUniqueCentreLocalHom.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.existsUnique_centre_local_hom : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (p : Cpt ξ) (R : Type) [CommRing R] [IsLocalRing R] (φ : regAt ξ p →+* R), IsLocalHom φ → ∃! z : Spec (CommRingCat.of R) ⟶ X, centre z = p.1 ∧ ∀ a : regAt ξ p, ValAt ξ z (a : Ω) (φ a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_unique_point_of_local | exact GlobalTheory.CompanionTheory.Ar.exists_unique_point_of_local | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_unique_point_of_local <;> assumption)
