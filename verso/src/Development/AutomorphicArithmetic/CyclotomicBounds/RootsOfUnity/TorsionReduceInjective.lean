import Mathlib

open NumberField IsDedekindDomain Classical

noncomputable section

namespace UpperTheory.Mu

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_one]`. Introduce `ζ hζ`. Assume the negation of the conclusion as `hne`. Establish `hmk : Ideal.Quotient.mk v.asIdeal (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L) = 1`. Establish `h` using `congrArg (fun u : (𝓞 L ⧸ v.asIdeal)ˣ => (u : 𝓞 L ⧸ v.asIdeal)) hζ`.

Simplify using `using h`. Establish `hx1 : (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L) ≠ 1`. Introduce `h`. Apply `hne` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `Units.ext h`. Establish `hpow : (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L) ^ NumberField.Units.torsionOrder L = 1`. Establish `h : ζ ^ Nat.card (NumberField.Units.torsion L) = 1` using `pow_card_eq_one'`. Use `show (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L) ^ Nat.card (NumberField.Units.torsion L) = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, h]`.

Simplify using the standard rewrite rules. Establish `hsum : ∑ i ∈ Finset.range (NumberField.Units.torsionOrder L), (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L) ^ i = 0`. Establish `h` using `geom_sum_mul (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L) (NumberField.Units.torsionOrder L)`. Rewrite `h` using `[hpow, sub_self]`. Conclude with `(mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hx1)`.

Apply `hw` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Establish `h` using `congrArg (Ideal.Quotient.mk v.asIdeal) hsum`. Rewrite `h` using `[map_sum, map_zero]`. Simplify using `only [map_pow, hmk, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h`.

Simplify using `using h`.
-/
theorem torsion_reduce_injective (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))
    (hw : ((NumberField.Units.torsionOrder L : ℕ) : 𝓞 L) ∉ v.asIdeal) :
    Function.Injective ((Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom).comp
      (NumberField.Units.torsion L).subtype) := by
  rw [injective_iff_map_eq_one]
  intro ζ hζ
  by_contra hne
  have hmk : Ideal.Quotient.mk v.asIdeal (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L) = 1 := by
    have h := congrArg (fun u : (𝓞 L ⧸ v.asIdeal)ˣ => (u : 𝓞 L ⧸ v.asIdeal)) hζ
    simpa using h
  have hx1 : (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L) ≠ 1 := by
    intro h
    apply hne
    apply Subtype.ext
    exact Units.ext h
  have hpow : (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L) ^ NumberField.Units.torsionOrder L = 1 := by
    have h : ζ ^ Nat.card (NumberField.Units.torsion L) = 1 := pow_card_eq_one'
    show (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L) ^ Nat.card (NumberField.Units.torsion L) = 1
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, h]
    simp
  have hsum : ∑ i ∈ Finset.range (NumberField.Units.torsionOrder L),
      (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L) ^ i = 0 := by
    have h := geom_sum_mul (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L)
      (NumberField.Units.torsionOrder L)
    rw [hpow, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hx1)
  apply hw
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h := congrArg (Ideal.Quotient.mk v.asIdeal) hsum
  rw [map_sum, map_zero] at h
  simp only [map_pow, hmk, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
  simpa using h

/- English proof (translation)
Introduce `L _ _ v hw hN ε`. Use `haveI := v.isMaximal`. Establish `hf` using `torsion_reduce_injective L v hw`. Use `set f := (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom).comp (NumberField.Units.torsion L).subtype with hf_def`. Establish `hcardk : Nat.card (𝓞 L ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal`.

Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `haveI : Finite (𝓞 L ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcardk]; omega)`. Set `e` to `MonoidHom.ofInjective hf`. Take `⟨θ0, hθ0⟩` from `MonoidHom.domRestrict_surjective (M := ℂ) f.range (ε.comp e.symm.toMonoidHom)`. Establish `hext : ∀ θ : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ, MonoidHom.domRestrictHom f.range ℂˣ θ = ε.comp e.symm.toMonoidHom → ∀ ζ : NumberField.Units.torsion L, θ (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom (ζ : (𝓞 L)ˣ)) = ε ζ`.

Introduce `θ hθ ζ`. Establish `h` using `DFunLike.congr_fun hθ (e ζ)`. Establish `h2 : e.symm (e ζ) = ζ` using `e.symm_apply_apply ζ`. Simplify using `only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, h2] at h`. Rewrite using `[← h]`.

Both sides reduce to the same expression. Establish `hS : Nat.card f.range = NumberField.Units.torsionOrder L`. Rewrite using `[← Nat.card_congr e.toEquiv]`. Both sides reduce to the same expression. Establish `hG : Nat.card (𝓞 L ⧸ v.asIdeal)ˣ = Ideal.absNorm v.asIdeal - 1`.

Use `letI : Field (𝓞 L ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal`. Establish `h` using `Nat.card_units (𝓞 L ⧸ v.asIdeal)`. Rewrite `h` using `[hcardk]`. Conclude with `h`. Establish `hq : 2 ≤ Nat.card ((𝓞 L ⧸ v.asIdeal)ˣ ⧸ f.range)`.

Establish `h` using `f.range.card_eq_card_quotient_mul_card_subgroup`. Rewrite `h` using `[hG, hS]`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Apply the tactic sequence `interval_cases hc : Nat.card ((𝓞 L ⧸ v.asIdeal)ˣ ⧸ f.range) <;> omega`.

Establish `hker : 2 ≤ Nat.card (MonoidHom.domRestrictHom f.range ℂˣ).ker`. Rewrite using `[CommGroup.card_domRestrictHom_ker]`. Conclude with `hq`. Use `haveI : Finite (MonoidHom.domRestrictHom f.range ℂˣ).ker := Nat.finite_of_card_ne_zero (by omega)`. Use `haveI : Nontrivial (MonoidHom.domRestrictHom f.range ℂˣ).ker := Finite.one_lt_card_iff_nontrivial.1 (by omega)`.

Take `⟨χ, hχ⟩` from `exists_ne (1 : (MonoidHom.domRestrictHom f.range ℂˣ).ker)`. Distinguish the cases in `h0 : θ0 = 1`. Use `⟨θ0 * χ.1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h0, one_mul]`. Introduce `h`.

Conclude with `hχ (Subtype.ext h)`. Apply `hext` to reduce the goal to its premises. Rewrite using `[map_mul, hθ0, MonoidHom.mem_ker.1 χ.2, mul_one]`. Conclude with `⟨θ0, h0, hext θ0 hθ0⟩`.
-/
theorem tame_ext : ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)), ((NumberField.Units.torsionOrder L : ℕ) : 𝓞 L) ∉ v.asIdeal → NumberField.Units.torsionOrder L + 1 < Ideal.absNorm v.asIdeal → ∀ ε : NumberField.Units.torsion L →* ℂˣ, ∃ θ : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ, θ ≠ 1 ∧ ∀ ζ : NumberField.Units.torsion L, θ (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom (ζ : (𝓞 L)ˣ)) = ε ζ := by
  intro L _ _ v hw hN ε
  haveI := v.isMaximal
  have hf := torsion_reduce_injective L v hw
  set f := (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom).comp
    (NumberField.Units.torsion L).subtype with hf_def
  have hcardk : Nat.card (𝓞 L ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcardk]; omega)
  let e := MonoidHom.ofInjective hf
  obtain ⟨θ0, hθ0⟩ := MonoidHom.domRestrict_surjective (M := ℂ) f.range (ε.comp e.symm.toMonoidHom)
  have hext : ∀ θ : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ,
      MonoidHom.domRestrictHom f.range ℂˣ θ = ε.comp e.symm.toMonoidHom →
      ∀ ζ : NumberField.Units.torsion L,
        θ (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom (ζ : (𝓞 L)ˣ)) = ε ζ := by
    intro θ hθ ζ
    have h := DFunLike.congr_fun hθ (e ζ)
    have h2 : e.symm (e ζ) = ζ := e.symm_apply_apply ζ
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, h2] at h
    rw [← h]
    rfl
  have hS : Nat.card f.range = NumberField.Units.torsionOrder L := by
    rw [← Nat.card_congr e.toEquiv]
    rfl
  have hG : Nat.card (𝓞 L ⧸ v.asIdeal)ˣ = Ideal.absNorm v.asIdeal - 1 := by
    letI : Field (𝓞 L ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    have h := Nat.card_units (𝓞 L ⧸ v.asIdeal)
    rw [hcardk] at h
    exact h
  have hq : 2 ≤ Nat.card ((𝓞 L ⧸ v.asIdeal)ˣ ⧸ f.range) := by
    have h := f.range.card_eq_card_quotient_mul_card_subgroup
    rw [hG, hS] at h
    by_contra hlt
    push_neg at hlt
    interval_cases hc : Nat.card ((𝓞 L ⧸ v.asIdeal)ˣ ⧸ f.range) <;> omega
  have hker : 2 ≤ Nat.card (MonoidHom.domRestrictHom f.range ℂˣ).ker := by
    rw [CommGroup.card_domRestrictHom_ker]
    exact hq
  haveI : Finite (MonoidHom.domRestrictHom f.range ℂˣ).ker := Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial (MonoidHom.domRestrictHom f.range ℂˣ).ker :=
    Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨χ, hχ⟩ := exists_ne (1 : (MonoidHom.domRestrictHom f.range ℂˣ).ker)
  by_cases h0 : θ0 = 1
  · refine ⟨θ0 * χ.1, ?_, ?_⟩
    · rw [h0, one_mul]
      intro h
      exact hχ (Subtype.ext h)
    · apply hext
      rw [map_mul, hθ0, MonoidHom.mem_ker.1 χ.2, mul_one]
  · exact ⟨θ0, h0, hext θ0 hθ0⟩

end UpperTheory.Mu
