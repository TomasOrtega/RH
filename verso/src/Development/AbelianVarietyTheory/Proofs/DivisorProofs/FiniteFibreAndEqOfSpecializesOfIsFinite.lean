import Mathlib

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `Y Y' k hk y`. Use `⟨k.finite_preimage_singleton y, ?_⟩` and prove the remaining obligations. Introduce `a b ha hb h`. Establish `hd` using `(k.isDiscrete_preimage_singleton y).to_subtype`. Establish `h' : (⟨a, ha⟩ : k ⁻¹' {y}) ⤳ ⟨b, hb⟩` using `Topology.IsInducing.subtypeVal.specializes_iff.mp h`.

Conclude with `congrArg Subtype.val h'.eq`.
-/
theorem finite_fibre_and_eq_of_specializes_of_isFinite :
    ∀ (Y Y' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ y : Y,
      {a : Y' | k a = y}.Finite ∧ ∀ a b : Y', k a = y → k b = y → a ⤳ b → a = b := by
  intro Y Y' k hk y
  refine ⟨k.finite_preimage_singleton y, ?_⟩
  intro a b ha hb h
  have hd := (k.isDiscrete_preimage_singleton y).to_subtype
  have h' : (⟨a, ha⟩ : k ⁻¹' {y}) ⤳ ⟨b, hb⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val h'.eq

end GlobalTheory
