import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sum_cubeSign_card_two {κ : Type} [LinearOrder κ] (t : Finset κ) (h : t.card = 2) :
    ∑ i ∈ t, GlobalTheory.cubeSign t i = 0 := by
  have key : ∀ x y : κ, x < y → ∑ i ∈ ({x, y} : Finset κ), GlobalTheory.cubeSign {x, y} i = 0 := by
    intro x y hxy
    rw [Finset.sum_pair hxy.ne]
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, hxy, hxy.not_gt]
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 h
  rcases lt_or_gt_of_ne hxy with h' | h'
  · exact key x y h'
  · rw [Finset.pair_comm]; exact key y x h'

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem δ_zero_one : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R), δ F 0 (fun _ => 1) = 0 := by
  intro κ _ R _ F
  funext t
  rw [δ_apply]
  simp only [map_one, Pi.zero_apply]
  rw [← Finset.sum_smul, Finset.sum_coe_sort t.1 (fun i => GlobalTheory.cubeSign t.1 i),
    sum_cubeSign_card_two t.1 t.2, zero_smul]

end GlobalTheory.CechPoset
