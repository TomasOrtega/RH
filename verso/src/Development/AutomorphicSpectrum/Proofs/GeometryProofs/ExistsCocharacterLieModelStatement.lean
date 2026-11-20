import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCocharacterLieModel
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.TorusLie.exists_lieModel_splitTorus` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FExistsCocharacterLieModel.lean&line=102#L102)
-/
theorem _root_.GlobalTheory.T.exists_cocharacter_lie_model : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (R : Type) [CommRing R] (x : Sp R ⟶ S), ∃ M : LieModel (splitTorus S X) x (X →+ R), IsCocharLie M := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusLie.exists_lieModel_splitTorus | exact GlobalTheory.CompanionTheory.Ar.TorusLie.exists_lieModel_splitTorus | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusLie.exists_lieModel_splitTorus <;> assumption)
