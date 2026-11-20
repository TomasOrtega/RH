import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedBaseChangeIffFibers
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_pullback_snd_spMap_iff_residueField` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FGeometricallyConnectedBaseChangeIffFibers.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.geometricallyConnected_baseChange_iff_fibers : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k), GeometricallyConnected (pullback.snd p (spMap (algebraMap k V))) ↔ ∀ x ∈ Set.range (PrimeSpectrum.comap (algebraMap k V)), GeometricallyConnected (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_pullback_snd_spMap_iff_residueField | exact GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_pullback_snd_spMap_iff_residueField | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_pullback_snd_spMap_iff_residueField <;> assumption)
