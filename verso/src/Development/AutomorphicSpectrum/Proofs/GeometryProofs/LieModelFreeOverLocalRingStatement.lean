import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOverLocalRing
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.LieFreeSmooth.lieModel_free_of_smooth` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLieModelFreeOverLocalRing.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.lie_model_free_over_local_ring : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R E) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieFreeSmooth.lieModel_free_of_smooth | exact GlobalTheory.CompanionTheory.Ar.LieFreeSmooth.lieModel_free_of_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.LieFreeSmooth.lieModel_free_of_smooth <;> assumption)
