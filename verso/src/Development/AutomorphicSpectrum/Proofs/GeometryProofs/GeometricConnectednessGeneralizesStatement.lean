import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricConnectednessGeneralizes
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
Apply `GlobalTheory.CompanionTheory.Ar.Approx.stableUnderGeneralization_geometricallyConnected_fibre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FGeometricConnectednessGeneralizes.lean&line=104#L104)
-/
theorem _root_.GlobalTheory.T.geometric_connectedness_generalizes : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (e : Sp k ⟶ X), e ≫ p = 𝟙 _ → Smooth p → IsProper p → StableUnderGeneralization {x : PrimeSpectrum k | GeometricallyConnected (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.stableUnderGeneralization_geometricallyConnected_fibre | exact GlobalTheory.CompanionTheory.Ar.Approx.stableUnderGeneralization_geometricallyConnected_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.stableUnderGeneralization_geometricallyConnected_fibre <;> assumption)
