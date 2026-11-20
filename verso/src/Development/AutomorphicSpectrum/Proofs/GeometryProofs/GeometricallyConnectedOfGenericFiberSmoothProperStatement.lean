import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedOfGenericFiberSmoothProper
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_generic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FGeometricallyConnectedOfGenericFiberSmoothProper.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.geometricallyConnected_of_generic_fiber_smooth_proper : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom → GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap R K))) → GeometricallyConnected G.hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_generic | exact GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_generic | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_generic <;> assumption)
