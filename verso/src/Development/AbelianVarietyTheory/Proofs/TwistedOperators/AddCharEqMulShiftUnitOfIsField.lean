import Mathlib

namespace GlobalTheory.Twist

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem addChar_eq_mulShift_unit_of_isField :
    ∀ {κf : Type} [CommRing κf] [Finite κf], IsField κf → ∀ ψ φ : AddChar κf ℂ, ψ ≠ 1 → φ ≠ 1 →
      ∃ c : κfˣ, ∀ t, φ t = ψ ((c : κf) * t) := by
  intro κf _ _ hF ψ φ hψ _
  classical
  let _ : Field κf := hF.toField
  have _ : Fintype κf := Fintype.ofFinite κf

  have hinj : Function.Injective ψ.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hψ)

  have hbij : Function.Bijective ψ.mulShift :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, AddChar.card_eq.symm⟩
  obtain ⟨a, ha⟩ := hbij.2 φ
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ‹φ ≠ 1› (by rw [← ha, AddChar.mulShift_zero])
  refine ⟨Units.mk0 a ha0, fun t => ?_⟩
  rw [← ha, AddChar.mulShift_apply, Units.val_mk0]

end GlobalTheory.Twist
