import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfIsPullbackSurjectiveLft
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGeometricallyConnectedOfIsPullbackSurjectiveLft.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.geometricallyConnected_of_isPullback_surjective_lft : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π → ∀ (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π → GeometricallyConnected G'.hom → GeometricallyConnected G.hom := by
  first | exact @GlobalTheory.Mum.geometricallyConnected_of_isPullback_of_surjective | exact GlobalTheory.Mum.geometricallyConnected_of_isPullback_of_surjective | (intros; apply GlobalTheory.Mum.geometricallyConnected_of_isPullback_of_surjective <;> assumption)
