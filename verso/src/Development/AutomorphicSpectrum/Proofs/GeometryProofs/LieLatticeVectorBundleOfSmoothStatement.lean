import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeVectorBundleOfSmooth
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLieLatticeVectorBundleOfSmooth.lean&line=451#L451)
-/
theorem _root_.GlobalTheory.T.lie_lattice_vector_bundle_of_smooth : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E), IsCptGen ξ → SmoothOfRelativeDimension g G.hom → M.lat.IsVB g ⊤ ∧ M.omLat.IsVB g ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieLat_isVB | exact GlobalTheory.CompanionTheory.Ar.lieLat_isVB | (intros; apply GlobalTheory.CompanionTheory.Ar.lieLat_isVB <;> assumption)
