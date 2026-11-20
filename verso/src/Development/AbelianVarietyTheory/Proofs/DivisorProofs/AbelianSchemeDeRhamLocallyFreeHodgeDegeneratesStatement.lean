import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamLocallyFreeHodgeDegenerates
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AbCoh.abelianHodgeDeRham` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianSchemeDeRhamLocallyFreeHodgeDegenerates.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates : GlobalTheory.Published.AbelianHodgeDeRham := by
  first | exact @GlobalTheory.AbCoh.abelianHodgeDeRham | exact GlobalTheory.AbCoh.abelianHodgeDeRham | (intros; apply GlobalTheory.AbCoh.abelianHodgeDeRham <;> assumption)
