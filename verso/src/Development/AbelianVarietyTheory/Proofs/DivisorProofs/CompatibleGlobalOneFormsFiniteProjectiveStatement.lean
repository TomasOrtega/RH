import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleGlobalOneFormsFiniteProjective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AbCoh.compatibleGlobalOneForms_finite_projective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCompatibleGlobalOneFormsFiniteProjective.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.glob1_finite_and_projective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → Module.Finite R (Glob1 F) ∧ Module.Projective R (Glob1 F) := by
  first | exact @GlobalTheory.AbCoh.compatibleGlobalOneForms_finite_projective | exact GlobalTheory.AbCoh.compatibleGlobalOneForms_finite_projective | (intros; apply GlobalTheory.AbCoh.compatibleGlobalOneForms_finite_projective <;> assumption)
