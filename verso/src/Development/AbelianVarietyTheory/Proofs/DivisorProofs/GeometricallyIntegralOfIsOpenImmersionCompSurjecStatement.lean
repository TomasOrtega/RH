import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIntegralOfIsOpenImmersionCompSurjec
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
Apply `GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGeometricallyIntegralOfIsOpenImmersionCompSurjec.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.geometricallyIntegral_comp_of_isOpenImmersion_surjective : ∀ (O Z T : Scheme.{0}) (j : O ⟶ Z) (f : Z ⟶ T) [IsOpenImmersion j] [GeometricallyIntegral f], Surjective (j ≫ f) → GeometricallyIntegral (j ≫ f) := by
  first | exact @GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective | exact GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective | (intros; apply GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective <;> assumption)
