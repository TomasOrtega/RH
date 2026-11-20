import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLieModelFiniteProjective.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.lie_model_finite_projective : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Module.Finite R E ∧ Module.Projective R E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective | exact GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective <;> assumption)
