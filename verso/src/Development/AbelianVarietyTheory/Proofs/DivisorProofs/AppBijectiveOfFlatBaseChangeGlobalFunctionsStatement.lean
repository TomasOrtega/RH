import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctions
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.app_bijective_of_flat_baseChange` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAppBijectiveOfFlatBaseChangeGlobalFunctions.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.app_bijective_of_flat_baseChange_globalFunctions : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), QuasiCompact π → QuasiSeparated π → Function.Bijective π.appTop.hom → Flat y → IsPullback p q y π → ∀ V : Y.Opens, Function.Bijective (p.app V).hom := by
  first | exact @GlobalTheory.Mum.app_bijective_of_flat_baseChange | exact GlobalTheory.Mum.app_bijective_of_flat_baseChange | (intros; apply GlobalTheory.Mum.app_bijective_of_flat_baseChange <;> assumption)
