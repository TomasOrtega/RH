import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquiv
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.lieModel_existsUnique_equiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLieModelExistsUniqueEquiv.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.lie_model_existsUnique_equiv : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E'] (M : LieModel G x E) (M' : LieModel G x E'), ∃! f : E ≃ₗ[R] E', ∀ e, M'.pt (f e) = M.pt e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_existsUnique_equiv | exact GlobalTheory.CompanionTheory.Ar.lieModel_existsUnique_equiv | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_existsUnique_equiv <;> assumption)
