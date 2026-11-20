import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesVanishingNoetherianAbelian
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AbCoh.AxesSq.axesO1_of_isAbelianScheme` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAxesVanishingNoetherianAbelian.lean&line=121#L121)
-/
theorem _root_.GlobalTheory.T.axes_vanishing_noetherian_abelian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → AxesVanishingStructureSheafDegOne A := by
  first | exact @GlobalTheory.AbCoh.AxesSq.axesO1_of_isAbelianScheme | exact GlobalTheory.AbCoh.AxesSq.axesO1_of_isAbelianScheme | (intros; apply GlobalTheory.AbCoh.AxesSq.axesO1_of_isAbelianScheme <;> assumption)
