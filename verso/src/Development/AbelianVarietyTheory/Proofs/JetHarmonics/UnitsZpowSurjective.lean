import Mathlib

namespace GlobalTheory.DivisibleUnits

/- English proof (translation)
Establish `nat_root : ∀ (m : ℕ), 0 < m → ∀ x : Fˣ, ∃ y : Fˣ, y ^ m = x`. Introduce `m hm x`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (x : F) hm`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hz` using `[zero_pow hm.ne']`. Conclude with `x.ne_zero hz.symm`. Use `⟨Units.mk0 z hz0, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `[hz]`.

Introduce `x`. Break down `Int.lt_or_gt_of_ne hn with h | h` into its components or cases. Take `⟨y, hy⟩` from `nat_root n.natAbs (Int.natAbs_pos.mpr hn) x⁻¹`. Use `⟨y, ?_⟩` and prove the remaining obligations. Use `show y ^ n = x`.

Establish `: n = -(n.natAbs : ℤ)` using `by omega`. Rewrite using `[this, zpow_neg, zpow_natCast, hy, inv_inv]`. Take `⟨y, hy⟩` from `nat_root n.natAbs (Int.natAbs_pos.mpr hn) x`. Use `⟨y, ?_⟩` and prove the remaining obligations. Use `show y ^ n = x`.

Establish `: n = (n.natAbs : ℤ)` using `by omega`. Rewrite using `[this, zpow_natCast, hy]`.
-/
theorem units_zpow_surjective {F : Type} [Field F] [IsAlgClosed F] {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun a : Fˣ => a ^ n) := by
  have nat_root : ∀ (m : ℕ), 0 < m → ∀ x : Fˣ, ∃ y : Fˣ, y ^ m = x := by
    intro m hm x
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : F) hm
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hm.ne'] at hz
      exact x.ne_zero hz.symm
    refine ⟨Units.mk0 z hz0, ?_⟩
    ext
    simp [hz]
  intro x
  rcases Int.lt_or_gt_of_ne hn with h | h
  · obtain ⟨y, hy⟩ := nat_root n.natAbs (Int.natAbs_pos.mpr hn) x⁻¹
    refine ⟨y, ?_⟩
    show y ^ n = x
    have : n = -(n.natAbs : ℤ) := by omega
    rw [this, zpow_neg, zpow_natCast, hy, inv_inv]
  · obtain ⟨y, hy⟩ := nat_root n.natAbs (Int.natAbs_pos.mpr hn) x
    refine ⟨y, ?_⟩
    show y ^ n = x
    have : n = (n.natAbs : ℤ) := by omega
    rw [this, zpow_natCast, hy]

noncomputable def divisibleUnits (F : Type) [Field F] [IsAlgClosed F] :
    DivisibleBy (Additive Fˣ) ℤ :=
  divisibleByOfSMulRightSurj (Additive Fˣ) ℤ (fun {n} hn x => by
    obtain ⟨y, hy⟩ := units_zpow_surjective (F := F) hn (Additive.toMul x)
    exact ⟨Additive.ofMul y, by simpa using congrArg Additive.ofMul hy⟩)

/- English proof (translation)
Use `letI := divisibleUnits F`. Take `⟨h, hh⟩` from `(Module.Baer.of_divisible (Additive Fˣ)).extension_property_addMonoidHom (MonoidHom.toAdditive Φ) hΦ (MonoidHom.toAdditive χ)`. Use `⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩` and prove the remaining obligations. Use `DFunLike.congr_fun hh (Additive.ofMul x)` as an intermediate fact. Conclude with `this`.
-/
theorem exists_extension {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (hΦ : Function.Injective Φ) (χ : H →* Fˣ) :
    ∃ κ : M →* Fˣ, ∀ x : H, κ (Φ x) = χ x := by
  letI := divisibleUnits F
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive Fˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive Φ) hΦ (MonoidHom.toAdditive χ)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  have := DFunLike.congr_fun hh (Additive.ofMul x)
  exact this

/- English proof (translation)
Introduce `Φ hΦ χ` and use `exists_extension Φ hΦ χ`.
-/
theorem target : ∀ {H M F : Type} [inst : CommGroup H] [inst_1 : CommGroup M] [inst_2 : Field F] [IsAlgClosed F] (Φ : H →* M), Function.Injective (⇑Φ : H → M) → ∀ (χ : H →* Fˣ), ∃ (κ : M →* Fˣ), ∀ (x : H), (κ : M → Fˣ) ((Φ : H → M) x) = (χ : H → Fˣ) x :=
  fun Φ hΦ χ => exists_extension Φ hΦ χ

end GlobalTheory.DivisibleUnits
