import Mathlib
import Formalism.PeriodIntegrals.CharExtend

namespace PI.CharExtendWork

/- English proof (translation)
Establish `hpos : 0 < n.natAbs` using `Int.natAbs_pos.mpr hn`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (a : ℂ) hpos`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Rewrite `hz` using `[zero_pow hpos.ne']`.

Conclude with `a.ne_zero hz.symm`. Use `set u : ℂˣ := Units.mk0 z hz0 with hu`. Establish `hu' : u ^ n.natAbs = a`. Use `ext`. Simplify using `[hu, hz]`.

Break down `Int.natAbs_eq n with h | h` into its components or cases. Use `⟨u, ?_⟩` and prove the remaining obligations. Rewrite using `[h, zpow_natCast, hu']`. Use `⟨u⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[h, inv_zpow', neg_neg, zpow_natCast, hu']`.
-/
theorem units_complex_exists_zpow (a : ℂˣ) (n : ℤ) (hn : n ≠ 0) : ∃ x : ℂˣ, x ^ n = a := by
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ) hpos
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hz
    exact a.ne_zero hz.symm
  set u : ℂˣ := Units.mk0 z hz0 with hu
  have hu' : u ^ n.natAbs = a := by
    ext
    simp [hu, hz]
  rcases Int.natAbs_eq n with h | h
  · refine ⟨u, ?_⟩
    rw [h, zpow_natCast, hu']
  · refine ⟨u⁻¹, ?_⟩
    rw [h, inv_zpow', neg_neg, zpow_natCast, hu']

noncomputable def divisibleUnitsComplex : DivisibleBy (Additive ℂˣ) ℤ where
  div a n := if h : n = 0 then 0 else
    Additive.ofMul (Classical.choose (units_complex_exists_zpow a.toMul n h))
  div_zero a := by simp
  div_cancel {n} a hn := by
    rw [dif_neg hn, ← ofMul_zpow, Classical.choose_spec (units_complex_exists_zpow a.toMul n hn)]
    rfl

/- English proof (translation)
Introduce `G _ H χ`. Use `letI : DivisibleBy (Additive ℂˣ) ℤ := divisibleUnitsComplex`. Establish `hB : Module.Baer ℤ (Additive ℂˣ)` using `Module.Baer.of_divisible (Additive ℂˣ)`. Set `f : Additive H →+ Additive G` to `MonoidHom.toAdditive H.subtype`. Establish `hf : Function.Injective f`.

Introduce `x y hxy`. Conclude with `Subtype.val_injective hxy`. Take `⟨h, hh⟩` from `hB.extension_property_addMonoidHom f hf (MonoidHom.toAdditive χ)`. Use `⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩` and prove the remaining obligations. Use `DFunLike.congr_fun hh (Additive.ofMul x)` as an intermediate fact.

Conclude with `this`.
-/
theorem charExtend_main : PI.CharExtend := by
  intro G _ H χ
  letI : DivisibleBy (Additive ℂˣ) ℤ := divisibleUnitsComplex
  have hB : Module.Baer ℤ (Additive ℂˣ) := Module.Baer.of_divisible (Additive ℂˣ)
  let f : Additive H →+ Additive G := MonoidHom.toAdditive H.subtype
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.val_injective hxy
  obtain ⟨h, hh⟩ := hB.extension_property_addMonoidHom f hf (MonoidHom.toAdditive χ)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  have := DFunLike.congr_fun hh (Additive.ofMul x)
  exact this

end PI.CharExtendWork
