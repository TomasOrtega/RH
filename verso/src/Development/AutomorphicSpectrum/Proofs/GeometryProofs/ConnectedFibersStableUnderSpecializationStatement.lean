import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedFibersStableUnderSpecialization
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Approx.stableUnderSpecialization_geometricallyConnected` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FConnectedFibersStableUnderSpecialization.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.connected_fibers_stableUnderSpecialization : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom → StableUnderSpecialization {x : PrimeSpectrum k | GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.stableUnderSpecialization_geometricallyConnected | exact GlobalTheory.CompanionTheory.Ar.Approx.stableUnderSpecialization_geometricallyConnected | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.stableUnderSpecialization_geometricallyConnected <;> assumption)
