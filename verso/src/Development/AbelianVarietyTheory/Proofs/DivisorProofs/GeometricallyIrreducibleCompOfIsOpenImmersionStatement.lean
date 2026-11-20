import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIrreducibleCompOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairUOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGeometricallyIrreducibleCompOfIsOpenImmersion.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.geometricallyIrreducible_comp_of_isOpenImmersion_surjective : ∀ (T W X : Scheme.{0}) (j : W ⟶ X), IsOpenImmersion j → ∀ (f : X ⟶ T), GeometricallyIrreducible f → Surjective (j ≫ f) → GeometricallyIrreducible (j ≫ f) := by
  first | exact @GlobalTheory.OpenGeomIrr.geometricallyIrreducible_comp_of_isOpenImmersion | exact GlobalTheory.OpenGeomIrr.geometricallyIrreducible_comp_of_isOpenImmersion | (intros; apply GlobalTheory.OpenGeomIrr.geometricallyIrreducible_comp_of_isOpenImmersion <;> assumption)
