import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2GeneratedByCups
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHyperH2GeneratedByCups.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.hyper_h2_generated_by_cups : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → Closed1 F = ⊤ → Function.Surjective (toO F) → WedgeO F → ∀ z : Hyp2 F, ∃ (n : ℕ) (a b : Fin n → Hyp1 F), z = ∑ k, cupHyp F (a k) (b k) := by
  first | exact @GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp | exact GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp | (intros; apply GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp <;> assumption)
