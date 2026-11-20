import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusPullbackAndVanishIntoLocus
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocusPull.locus_pull` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNonvanishingLocusPullbackAndVanishIntoLocus.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus : (∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (c : Pic X) (V : X.Opens), IsLocus c V → IsLocus (GlobalTheory.CechPic.pull f c) (f ⁻¹ᵁ V)) ∧ (∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (c : Pic X) (V : X.Opens), IsLocus c V → (∀ y, f y ∈ V) → GlobalTheory.CechPic.pull f c = 0) := by
  first | exact @GlobalTheory.LocusPull.locus_pull | exact GlobalTheory.LocusPull.locus_pull | (intros; apply GlobalTheory.LocusPull.locus_pull <;> assumption)
