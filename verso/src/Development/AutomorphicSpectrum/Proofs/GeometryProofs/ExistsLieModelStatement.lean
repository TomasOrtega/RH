import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FExistsLieModel.lean&line=255#L255)
-/
theorem _root_.GlobalTheory.T.exists_lie_model : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S), ∃ (E : Type) (_ : AddCommGroup E) (_ : Module R E), Nonempty (LieModel G x E) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_exists | exact GlobalTheory.CompanionTheory.Ar.lieModel_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_exists <;> assumption)
