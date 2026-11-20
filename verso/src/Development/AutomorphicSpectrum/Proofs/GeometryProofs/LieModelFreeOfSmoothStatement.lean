import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOfSmooth
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLieModelFreeOfSmooth.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.lie_model_free_of_smooth : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Nonempty (Module.Basis (Fin g) R E) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.lie_model_free_of_smooth | exact GlobalTheory.CompanionTheory.Relay.lie_model_free_of_smooth | (intros; apply GlobalTheory.CompanionTheory.Relay.lie_model_free_of_smooth <;> assumption)
