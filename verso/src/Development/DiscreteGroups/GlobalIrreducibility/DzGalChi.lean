import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.ExistsUniformizerValuation

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `x`. Establish `hg0 : (g : ℚ_[g]) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero`. Establish `hgk : (g : w.adicCompletion E) ≠ 0`. Rewrite using `[← map_natCast i]`. Conclude with `(map_ne_zero i).2 hg0`.

Use `set y : ℚ_[g] := i.symm (x : w.adicCompletion E) with hy`. Establish `hy0 : y ≠ 0` using `(map_ne_zero i.symm).2 x.ne_zero`. Establish `hn : ‖y * (g : ℚ_[g]) ^ (-y.valuation)‖ = 1`. Rewrite using `[norm_mul, Padic.norm_eq_zpow_neg_valuation hy0, Padic.norm_p_zpow, neg_neg, ← zpow_add₀, neg_add_cancel, zpow_zero]`. Conclude with `Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero`.

Set `γ : (w.adicCompletion E)ˣ` to `Units.mk0 _ hgk`. Establish `hγ : χ γ = 1` using `hlc.2 γ rfl`. Establish `hu` using `hlc.1 (PadicInt.mkUnits hn) (x * γ ^ (-y.valuation)) (by`. Rewrite using `[PadicInt.mkUnits_eq, map_mul, map_zpow₀, map_natCast, hy, RingEquiv.apply_symm_apply, Units.val_mul, Units.val_zpow_eq_zpow_val]`. Use the proof step `rfl)`.

Rewrite `hu` using `[map_mul, map_zpow, hγ, one_zpow, mul_one]`. Rewrite using `[hu, ← map_pow, ZMod.units_pow_card_sub_one_eq_one, map_one]`.
-/
theorem liftsChar_pow {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (χ₀ : (ZMod g)ˣ →* ℂˣ)
    (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hlc : LiftsChar i χ₀ χ) : ∀ x, χ x ^ (g - 1) = 1 := by
  intro x
  have hg0 : (g : ℚ_[g]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
  have hgk : (g : w.adicCompletion E) ≠ 0 := by
    rw [← map_natCast i]; exact (map_ne_zero i).2 hg0
  set y : ℚ_[g] := i.symm (x : w.adicCompletion E) with hy
  have hy0 : y ≠ 0 := (map_ne_zero i.symm).2 x.ne_zero
  have hn : ‖y * (g : ℚ_[g]) ^ (-y.valuation)‖ = 1 := by
    rw [norm_mul, Padic.norm_eq_zpow_neg_valuation hy0, Padic.norm_p_zpow, neg_neg, ← zpow_add₀, neg_add_cancel,
      zpow_zero]
    exact Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
  let γ : (w.adicCompletion E)ˣ := Units.mk0 _ hgk
  have hγ : χ γ = 1 := hlc.2 γ rfl
  have hu := hlc.1 (PadicInt.mkUnits hn) (x * γ ^ (-y.valuation)) (by
    rw [PadicInt.mkUnits_eq, map_mul, map_zpow₀, map_natCast, hy, RingEquiv.apply_symm_apply, Units.val_mul,
      Units.val_zpow_eq_zpow_val]
    rfl)
  rw [map_mul, map_zpow, hγ, one_zpow, mul_one] at hu
  rw [hu, ← map_pow, ZMod.units_pow_card_sub_one_eq_one, map_one]

/- English proof (translation)
Establish `hv` using `Valuation.integer.integers (valuation k)`. Use `⟨fun x hx => ?_, fun b hb => ?_⟩` and prove the remaining obligations. Set `a : 𝒪[k]` to `⟨x, (Valuation.mem_integer_iff _ _).2 hx.1.le⟩`. Establish `ha : IsUnit a` using `hv.isUnit_iff_valuation_eq_one.2 hx.1`. Establish `e : Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) ha.unit = x` using `Units.ext rfl`.

Establish `e' : Units.map (IsLocalRing.residue 𝒪[k] : 𝒪[k] →* 𝓀[k]) ha.unit = 1`. Use `Units.ext ?_` and prove the remaining obligations. Use `show IsLocalRing.residue 𝒪[k] a = 1`. Rewrite using `[← map_one (IsLocalRing.residue 𝒪[k]), residue_eq_iff_valuation_lt]`. Establish `h2` using `hx.2`.

Rewrite `h2` using `[pow_one]`. Conclude with `lt_of_le_of_lt h2 uniformizer_lt_one`. Rewrite using `[← e, hcompat, e', map_one]`. Take `rfl : b = 0` from `by omega`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z, ζb z ≠ 1 := by`.

Assume the negation of the conclusion as `h`. Conclude with `hne (MonoidHom.ext fun z => not_not.1 (not_exists.1 h z))`. Take `⟨a, ha⟩` from `IsLocalRing.residue_surjective (z : 𝓀[k])`. Establish `hau : IsUnit a` using `(IsLocalRing.residue_ne_zero_iff_isUnit a).1 (ha ▸ z.ne_zero)`. Establish `h1 : valuation k ((Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) hau.unit : kˣ) : k) = 1` using `hv.isUnit_iff_valuation_eq_one.1 hau`.

Use `⟨_, ⟨h1, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero]`. Conclude with `(Valuation.map_sub _ _ _).trans (by rw [h1, map_one, max_self])`. Rewrite using `[hcompat]`. Establish `: Units.map (IsLocalRing.residue 𝒪[k] : 𝒪[k] →* 𝓀[k]) hau.unit = z` using `Units.ext ha`.

Rewrite using `[this]` and apply the resulting hypothesis.
-/
theorem hasExponent_one_of_res {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ζ : kˣ →* ℂˣ) (ζb : 𝓀[k]ˣ →* ℂˣ)
    (hcompat : ∀ x : 𝒪[k]ˣ, ζ (Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) x) =
      ζb (Units.map (IsLocalRing.residue 𝒪[k] : 𝒪[k] →* 𝓀[k]) x)) (hne : ζb ≠ 1) : HasExponent ζ 1 := by
  have hv := Valuation.integer.integers (valuation k)
  refine ⟨fun x hx => ?_, fun b hb => ?_⟩
  · let a : 𝒪[k] := ⟨x, (Valuation.mem_integer_iff _ _).2 hx.1.le⟩
    have ha : IsUnit a := hv.isUnit_iff_valuation_eq_one.2 hx.1
    have e : Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) ha.unit = x := Units.ext rfl
    have e' : Units.map (IsLocalRing.residue 𝒪[k] : 𝒪[k] →* 𝓀[k]) ha.unit = 1 := by
      refine Units.ext ?_
      show IsLocalRing.residue 𝒪[k] a = 1
      rw [← map_one (IsLocalRing.residue 𝒪[k]), residue_eq_iff_valuation_lt]
      have h2 := hx.2
      rw [pow_one] at h2
      exact lt_of_le_of_lt h2 uniformizer_lt_one
    rw [← e, hcompat, e', map_one]
  · obtain rfl : b = 0 := by omega
    obtain ⟨z, hz⟩ : ∃ z, ζb z ≠ 1 := by
      by_contra h
      exact hne (MonoidHom.ext fun z => not_not.1 (not_exists.1 h z))
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (z : 𝓀[k])
    have hau : IsUnit a := (IsLocalRing.residue_ne_zero_iff_isUnit a).1 (ha ▸ z.ne_zero)
    have h1 : valuation k ((Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) hau.unit : kˣ) : k) = 1 :=
      hv.isUnit_iff_valuation_eq_one.1 hau
    refine ⟨_, ⟨h1, ?_⟩, ?_⟩
    · rw [pow_zero]
      exact (Valuation.map_sub _ _ _).trans (by rw [h1, map_one, max_self])
    · rw [hcompat]
      have : Units.map (IsLocalRing.residue 𝒪[k] : 𝒪[k] →* 𝓀[k]) hau.unit = z := Units.ext ha
      rwa [this]

end DiscreteGroups.sglob.DzType
