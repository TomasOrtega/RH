import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCompatibleFamilyToIntersectionsBijective
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
Apply `GlobalTheory.CechPoset.restrictCompatibleFamilyToIntersections_bijective` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRestrictCompatibleFamilyToIntersectionsBijective.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.res0_bijective_of_affine_intersections_of_iSup_eq_top : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)), ⨆ i, D i = ⊤ → Function.Bijective (res0 s D hD) := by
  first | exact @GlobalTheory.CechPoset.restrictCompatibleFamilyToIntersections_bijective | exact GlobalTheory.CechPoset.restrictCompatibleFamilyToIntersections_bijective | (intros; apply GlobalTheory.CechPoset.restrictCompatibleFamilyToIntersections_bijective <;> assumption)
