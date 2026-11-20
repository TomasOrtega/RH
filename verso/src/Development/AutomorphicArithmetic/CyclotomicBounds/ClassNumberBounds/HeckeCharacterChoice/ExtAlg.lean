import Mathlib

namespace KStar.Choice

def IsDiv (A : Type*) [CommGroup A] : Prop :=
  ∀ n : ℕ, n ≠ 0 → Function.Surjective fun a : A => a ^ n

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isDiv_complex_circle : IsDiv ℂˣ ∧ IsDiv Circle := by
  refine ⟨fun n hn z => ?_, fun n hn z => ?_⟩
  · obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) (Nat.pos_of_ne_zero hn)
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hw
      exact z.ne_zero hw.symm
    refine ⟨Units.mk0 w hw0, ?_⟩
    ext
    simp [hw]
  · refine ⟨Circle.exp ((z : ℂ).arg / n), ?_⟩
    simp only
    rw [← Circle.exp_natCast_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn), Circle.exp_arg]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Equip the data with the indicated structure. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem IsDiv.exists_extension {G A : Type*} [CommGroup G] [CommGroup A] (hA : IsDiv A)
    (H : Subgroup G) (f : H →* A) : ∃ F : G →* A, ∀ h : H, F h = f h := by
  have hsurj : ∀ {n : ℤ}, n ≠ 0 → Function.Surjective fun a : Additive A => n • a := by
    intro n hn x
    obtain ⟨y, hy⟩ := hA n.natAbs (Int.natAbs_ne_zero.mpr hn) (Additive.toMul x)
    rcases Int.natAbs_eq n with h | h
    · refine ⟨Additive.ofMul y, ?_⟩
      rw [h]
      change Additive.ofMul (y ^ ((n.natAbs : ℕ) : ℤ)) = x
      rw [zpow_natCast]
      simp only at hy
      rw [hy]
      rfl
    · refine ⟨Additive.ofMul y⁻¹, ?_⟩
      rw [h]
      change Additive.ofMul (y⁻¹ ^ (-((n.natAbs : ℕ) : ℤ))) = x
      rw [inv_zpow', neg_neg, zpow_natCast]
      simp only at hy
      rw [hy]
      rfl
  letI : DivisibleBy (Additive A) ℤ := divisibleByOfSMulRightSurj _ _ hsurj
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive A)).extension_property_addMonoidHom
    (MonoidHom.toAdditive H.subtype) Subtype.val_injective (MonoidHom.toAdditive f)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  exact congrArg Additive.toMul (DFunLike.congr_fun hh (Additive.ofMul x))

end KStar.Choice
