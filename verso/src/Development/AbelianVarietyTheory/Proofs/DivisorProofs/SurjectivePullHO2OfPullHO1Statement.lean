import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePullHO2OfPullHO1
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AbCoh.pullHO2_surjective_of_wedge` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSurjectivePullHO2OfPullHO1.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.surjective_pullHO2_of_pullHO1 : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ), Function.Surjective (pullHO1 h) → WedgeO (OAff s') → Function.Surjective (pullHO2 h) := by
  first | exact @GlobalTheory.AbCoh.pullHO2_surjective_of_wedge | exact GlobalTheory.AbCoh.pullHO2_surjective_of_wedge | (intros; apply GlobalTheory.AbCoh.pullHO2_surjective_of_wedge <;> assumption)
