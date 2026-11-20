import Mathlib

namespace GlobalTheory.ExtensionCharacter

/- English proof (translation)
Introduce `x`. Establish `hpos : 0 < n.natAbs` using `Int.natAbs_pos.mpr hn`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq ((x : F)) hpos`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hz` using `[zero_pow hpos.ne']`. Conclude with `x.ne_zero hz.symm`. Establish `hu : (Units.mk0 z hz0) ^ n.natAbs = x` using `by ext; simp [hz]`. Break down `Int.natAbs_eq n with h | h` into its components or cases. Use `⟨Units.mk0 z hz0, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[h, zpow_natCast, hu]`. Use `⟨(Units.mk0 z hz0)⁻¹, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[h, inv_zpow', neg_neg, zpow_natCast, hu]`.
-/
theorem units_zpow_surjective {F : Type} [Field F] [IsAlgClosed F] {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun u : Fˣ => u ^ n) := by
  intro x
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((x : F)) hpos
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hz
    exact x.ne_zero hz.symm
  have hu : (Units.mk0 z hz0) ^ n.natAbs = x := by
    ext; simp [hz]
  rcases Int.natAbs_eq n with h | h
  · refine ⟨Units.mk0 z hz0, ?_⟩
    simp only
    rw [h, zpow_natCast, hu]
  · refine ⟨(Units.mk0 z hz0)⁻¹, ?_⟩
    simp only
    rw [h, inv_zpow', neg_neg, zpow_natCast, hu]

noncomputable instance divisibleUnits (F : Type) [Field F] [IsAlgClosed F] :
    DivisibleBy (Additive Fˣ) ℤ :=
  divisibleByOfSMulRightSurj _ _ fun {n} hn x => by
    obtain ⟨y, hy⟩ := units_zpow_surjective (F := F) hn (Additive.toMul x)
    exact ⟨Additive.ofMul y, by simpa [ofMul_zpow] using congrArg Additive.ofMul hy⟩

/- English proof (translation)
Introduce `H M F _ _ _ _ Φ hΦ χ`. Take `⟨h, hh⟩` from `(Module.Baer.of_divisible (Additive Fˣ)).extension_property_addMonoidHom (MonoidHom.toAdditive Φ) hΦ (MonoidHom.toAdditive χ)`. Use `⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩` and prove the remaining obligations. Use `DFunLike.congr_fun hh (Additive.ofMul x)` as an intermediate fact. Conclude with `this`.
-/
theorem exists_extension_character : ∀ {H M F : Type} [inst : CommGroup H] [inst_1 : CommGroup M]
    [inst_2 : Field F] [IsAlgClosed F] (Φ : H →* M), Function.Injective (⇑Φ : H → M) →
    ∀ (χ : H →* Fˣ), ∃ (κ : M →* Fˣ), ∀ (x : H), (κ : M → Fˣ) ((Φ : H → M) x) = (χ : H → Fˣ) x := by
  intro H M F _ _ _ _ Φ hΦ χ
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive Fˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive Φ) hΦ (MonoidHom.toAdditive χ)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  have := DFunLike.congr_fun hh (Additive.ofMul x)
  exact this

end GlobalTheory.ExtensionCharacter
