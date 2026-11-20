import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusPointOverFractionField
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_eq_comp_pt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FTorusPointOverFractionField.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.torus_point_over_fraction_field : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (Ω : Type) [Field Ω] (k : FractionRing R →+* Ω) (y : Spec (CommRingCat.of Ω) ⟶ Γ.G.left), y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (k.comp (algebraMap R (FractionRing R)))) → ∃ t, y = Spec.map (CommRingCat.ofHom k) ≫ (Γ.pt t).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_eq_comp_pt | exact GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_eq_comp_pt | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_eq_comp_pt <;> assumption)
