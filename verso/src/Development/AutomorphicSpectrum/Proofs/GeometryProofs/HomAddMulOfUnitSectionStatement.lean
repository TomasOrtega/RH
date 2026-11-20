import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomAddMulOfUnitSection
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerRingInjective
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc.hom_add_mod_closed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FHomAddMulOfUnitSection.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.hom_add_mul_of_unit_section : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (G : Over S) [GrpObj G] (P V : Type) [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P] [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (u : ob x P ⟶ G), zsec x ≫ u = 1 → ∀ f g : P →ₗ[R] V, hom x (f + g) ≫ u = (hom x f ≫ u) * (hom x g ≫ u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc.hom_add_mod_closed | exact GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc.hom_add_mod_closed | (intros; apply GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc.hom_add_mod_closed <;> assumption)
