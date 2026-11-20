import Mathlib

namespace GlobalTheory.Twist

/- English proof (translation)
Introduce `κf _ _ hF ψ φ hψ _`. Set `_ : Field κf` to `hF.toField`. Establish `_ : Fintype κf` using `Fintype.ofFinite κf`. Establish `hinj : Function.Injective ψ.mulShift` using `AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hψ)`. Establish `hbij : Function.Bijective ψ.mulShift` using `(Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, AddChar.card_eq.symm⟩`.

Take `⟨a, ha⟩` from `hbij.2 φ`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `‹φ ≠ 1› (by rw [← ha, AddChar.mulShift_zero])`. Use `⟨Units.mk0 a ha0, fun t => ?_⟩` and prove the remaining obligations.

Rewrite using `[← ha, AddChar.mulShift_apply, Units.val_mk0]`.
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
