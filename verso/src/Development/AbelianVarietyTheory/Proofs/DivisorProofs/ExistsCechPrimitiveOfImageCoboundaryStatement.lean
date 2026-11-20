import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPrimitiveOfImageCoboundary
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCechPrimitiveOfImageCoboundary.lean&line=104#L104)
-/
theorem _root_.GlobalTheory.T.exists_cech_primitive_of_image_coboundary : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (z : CC F 1), δ F 1 z = 0 → ∀ g : C0 F, e1 F z = d0 F g → ∃ c : CC F 0, δ F 0 c = z := by
  first | exact @GlobalTheory.CechHOneInj.exists_cech_primitive | exact GlobalTheory.CechHOneInj.exists_cech_primitive | (intros; apply GlobalTheory.CechHOneInj.exists_cech_primitive <;> assumption)
