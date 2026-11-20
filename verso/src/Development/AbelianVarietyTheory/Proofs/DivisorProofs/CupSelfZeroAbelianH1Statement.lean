import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSelfZeroAbelianH1
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AbCoh.cup_self_eq_zero_of_isAbelianScheme` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCupSelfZeroAbelianH1.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.cup_self_zero_abelian_h1 : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ x : HO1 A.hom, cup _ x x = 0 := by
  first | exact @GlobalTheory.AbCoh.cup_self_eq_zero_of_isAbelianScheme | exact GlobalTheory.AbCoh.cup_self_eq_zero_of_isAbelianScheme | (intros; apply GlobalTheory.AbCoh.cup_self_eq_zero_of_isAbelianScheme <;> assumption)
