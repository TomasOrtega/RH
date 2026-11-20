import Mathlib

namespace KStar.Choice

def IsDiv (A : Type*) [CommGroup A] : Prop :=
  ∀ n : ℕ, n ≠ 0 → Function.Surjective fun a : A => a ^ n

/- English proof (translation)
Use `⟨fun n hn z => ?_, fun n hn z => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `IsAlgClosed.exists_pow_nat_eq (z : ℂ) (Nat.pos_of_ne_zero hn)`. Establish `hw0 : w ≠ 0`. Introduce and unpack `rfl`. Rewrite `hw` using `[zero_pow hn]`.

Conclude with `z.ne_zero hw.symm`. Use `⟨Units.mk0 w hw0, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `[hw]`. Use `⟨Circle.exp ((z : ℂ).arg / n), ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[← Circle.exp_natCast_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn), Circle.exp_arg]`.
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
Establish `hsurj : ∀ {n : ℤ}, n ≠ 0 → Function.Surjective fun a : Additive A => n • a`. Introduce `n hn x`. Take `⟨y, hy⟩` from `hA n.natAbs (Int.natAbs_ne_zero.mpr hn) (Additive.toMul x)`. Break down `Int.natAbs_eq n with h | h` into its components or cases. Use `⟨Additive.ofMul y, ?_⟩` and prove the remaining obligations.

Rewrite using `[h]`. Express the relevant statement in the definitionally equal form `Additive.ofMul (y ^ ((n.natAbs : ℕ) : ℤ)) = x`. Rewrite using `[zpow_natCast]`. Simplify using `only at hy`. Rewrite using `[hy]`.

Both sides reduce to the same expression. Use `⟨Additive.ofMul y⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[h]`. Express the relevant statement in the definitionally equal form `Additive.ofMul (y⁻¹ ^ (-((n.natAbs : ℕ) : ℤ))) = x`. Rewrite using `[inv_zpow', neg_neg, zpow_natCast]`.

Simplify using `only at hy`. Rewrite using `[hy]`. Both sides reduce to the same expression. Use `letI : DivisibleBy (Additive A) ℤ := divisibleByOfSMulRightSurj _ _ hsurj`. Take `⟨h, hh⟩` from `(Module.Baer.of_divisible (Additive A)).extension_property_addMonoidHom (MonoidHom.toAdditive H.subtype) Subtype.val_injective (MonoidHom.toAdditive f)`.

Use `⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩` and prove the remaining obligations. Conclude with `congrArg Additive.toMul (DFunLike.congr_fun hh (Additive.ofMul x))`.
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
