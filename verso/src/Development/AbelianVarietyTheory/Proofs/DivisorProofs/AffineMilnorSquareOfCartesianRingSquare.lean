import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualOpen

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem milnor_of_ring_square : ∀ (P C₁ C₂ C₀ : Type) [CommRing P] [CommRing C₁] [CommRing C₂] [CommRing C₀] (p₁ : P →+* C₁) (p₂ : P →+* C₂) (q₁ : C₁ →+* C₀) (q₂ : C₂ →+* C₀), q₁.comp p₁ = q₂.comp p₂ → (∀ x, p₁ x = 0 → p₂ x = 0 → x = 0) → (∀ a b, q₁ a = q₂ b → ∃ x, p₁ x = a ∧ p₂ x = b) → Function.Surjective q₂ → Milnor (spMap p₁) (spMap p₂) (spMap q₁) (spMap q₂) := by
  intro P C₁ C₂ C₀ _ _ _ _ p₁ p₂ q₁ q₂ hw hinj hsurj hq₂
  have hwc : CommRingCat.ofHom p₁ ≫ CommRingCat.ofHom q₁ = CommRingCat.ofHom p₂ ≫ CommRingCat.ofHom q₂ := by
    ext x; exact congrArg (fun f : P →+* C₀ => f x) hw
  have H : IsPullback (CommRingCat.ofHom p₁) (CommRingCat.ofHom p₂) (CommRingCat.ofHom q₁) (CommRingCat.ofHom q₂) := by
    refine IsPullback.of_map (forget CommRingCat) hwc ?_
    rw [Types.isPullback_iff]
    refine ⟨by rw [← Functor.map_comp, ← Functor.map_comp, hwc], ?_, ?_⟩
    · rintro x y ⟨h1, h2⟩
      have h1' : p₁ x = p₁ y := h1
      have h2' : p₂ x = p₂ y := h2
      exact sub_eq_zero.mp (hinj _ (by rw [map_sub, h1', sub_self]) (by rw [map_sub, h2', sub_self]))
    · intro a b hab
      exact hsurj a b hab
  refine ⟨inferInstance, inferInstance, inferInstance, IsClosedImmersion.spec_of_surjective _ hq₂, ?_, ?_⟩
  · simp only [spMap, ← Spec.map_comp, hwc]
  · refine IsPullback.of_iso H (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm
      (Scheme.ΓSpecIso _).symm ?_ ?_ ?_ ?_ <;>
    simp [spMap, Scheme.ΓSpecIso_inv_naturality]

end GlobalTheory.DualOpen
