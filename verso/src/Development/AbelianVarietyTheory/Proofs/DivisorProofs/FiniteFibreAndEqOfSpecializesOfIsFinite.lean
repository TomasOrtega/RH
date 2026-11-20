import Mathlib

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
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
