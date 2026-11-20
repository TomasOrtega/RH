import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CechDR.cmpO_injective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FStructureSheafComparisonInjective.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.structure_sheaf_comparison_injective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Function.Injective (cmpO s) := by
  first | exact @GlobalTheory.CechDR.cmpO_injective | exact GlobalTheory.CechDR.cmpO_injective | (intros; apply GlobalTheory.CechDR.cmpO_injective <;> assumption)
