import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Kummer

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

/- English proof (translation)
Rewrite using `[← QuotientAddGroup.mk_zsmul]`. Use `congr 1`. Rewrite using `[zsmul_eq_mul, mul_one_div]`.
-/
theorem nsmul_mk_one_div (n : ℕ) [NeZero n] (m : ℤ) :
    m • (QuotientAddGroup.mk (1 / (n : ℚ)) : QZ) = QuotientAddGroup.mk ((m : ℚ) / n) := by
  rw [← QuotientAddGroup.mk_zsmul]
  congr 1
  rw [zsmul_eq_mul, mul_one_div]

/- English proof (translation)
Rewrite using `[QuotientAddGroup.eq_zero_iff]`. Conclude with `Iff.rfl`.
-/
theorem mk_eq_zero_QZ (q : ℚ) : (QuotientAddGroup.mk q : QZ) = 0 ↔ ∃ k : ℤ, (k : ℚ) = q := by
  rw [QuotientAddGroup.eq_zero_iff]
  exact Iff.rfl

noncomputable def zmodToQZ (n : ℕ) [NeZero n] : ZMod n →+ QZ :=
  ZMod.lift n ⟨zmultiplesHom QZ (QuotientAddGroup.mk (1 / (n : ℚ))), by
    have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
    rw [zmultiplesHom_apply, nsmul_mk_one_div, mk_eq_zero_QZ]
    exact ⟨1, by rw [Int.cast_natCast, div_self hn, Int.cast_one]⟩⟩

/- English proof (translation)
Rewrite using `[zmodToQZ, ZMod.lift_coe]`. Use `show zmultiplesHom QZ (QuotientAddGroup.mk (1 / (n : ℚ))) m = _`. Rewrite using `[zmultiplesHom_apply, nsmul_mk_one_div]`.
-/
theorem zmodToQZ_intCast (n : ℕ) [NeZero n] (m : ℤ) :
    zmodToQZ n (m : ZMod n) = QuotientAddGroup.mk ((m : ℚ) / n) := by
  rw [zmodToQZ, ZMod.lift_coe]
  show zmultiplesHom QZ (QuotientAddGroup.mk (1 / (n : ℚ))) m = _
  rw [zmultiplesHom_apply, nsmul_mk_one_div]

/- English proof (translation)
Establish `hn : (n : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 (NeZero.ne n)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Take `⟨m, rfl⟩` from `ZMod.intCast_surjective a`. Rewrite `ha` using `[zmodToQZ_intCast, mk_eq_zero_QZ]`.

Take `⟨k, hk⟩` from `ha`. Rewrite using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite `hk` using `[eq_div_iff hn]`. Establish `: ((k * n : ℤ) : ℚ) = (m : ℚ)` using `by push_cast; exact hk`.

Rewrite using `[mul_comm]`. Conclude with `this.symm` after adjusting the coercions.
-/
theorem zmodToQZ_injective (n : ℕ) [NeZero n] : Injective (zmodToQZ n) := by
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective a
  rw [zmodToQZ_intCast, mk_eq_zero_QZ] at ha
  obtain ⟨k, hk⟩ := ha
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨k, ?_⟩
  rw [eq_div_iff hn] at hk
  have : ((k * n : ℤ) : ℚ) = (m : ℚ) := by push_cast; exact hk
  rw [mul_comm]
  exact_mod_cast this.symm

/- English proof (translation)
Establish `hn : (n : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 (NeZero.ne n)`. Take `⟨q, rfl⟩` from `QuotientAddGroup.mk_surjective x`. Rewrite `hx` using `[← QuotientAddGroup.mk_nsmul, mk_eq_zero_QZ]`. Take `⟨k, hk⟩` from `hx`. Use `⟨(k : ZMod n), ?_⟩` and prove the remaining obligations.

Rewrite using `[zmodToQZ_intCast, hk, nsmul_eq_mul, mul_div_cancel_left₀ _ hn]`.
-/
theorem exists_zmodToQZ_eq (n : ℕ) [NeZero n] (x : QZ) (hx : n • x = 0) : ∃ a, zmodToQZ n a = x := by
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [← QuotientAddGroup.mk_nsmul, mk_eq_zero_QZ] at hx
  obtain ⟨k, hk⟩ := hx
  refine ⟨(k : ZMod n), ?_⟩
  rw [zmodToQZ_intCast, hk, nsmul_eq_mul, mul_div_cancel_left₀ _ hn]

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) n`. Establish `h1 : g ζ = ζ` using `g.commutes ⟨ζ, hμ ζ hζ.pow_eq_one⟩`. Rewrite `h1` using `[cycN_spec g ζ hζ.pow_eq_one]`. Establish `h2 : ζ ^ ((cycK p K n g : (ZMod n)ˣ) : ZMod n).val = ζ ^ (1 % n)`. Rewrite using `[← pow_eq_pow_mod 1 hζ.pow_eq_one, pow_one]`.

Conclude with `h1`. Establish `h3` using `hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt 1 (Nat.pos_of_ne_zero (NeZero.ne n))) h2`. Rewrite `h3` using `[← ZMod.val_one_eq_one_mod]`. Conclude with `Units.ext (ZMod.val_injective n h3)`.
-/
theorem cycK_eq_one {n : ℕ} [NeZero n] (hμ : ∀ ζ : PadicAlgCl p, ζ ^ n = 1 → ζ ∈ K) (g : GK p K) :
    cycK p K n g = 1 := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) n
  have h1 : g ζ = ζ := g.commutes ⟨ζ, hμ ζ hζ.pow_eq_one⟩
  rw [cycN_spec g ζ hζ.pow_eq_one] at h1
  have h2 : ζ ^ ((cycK p K n g : (ZMod n)ˣ) : ZMod n).val = ζ ^ (1 % n) := by
    rw [← pow_eq_pow_mod 1 hζ.pow_eq_one, pow_one]
    exact h1
  have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt 1 (Nat.pos_of_ne_zero (NeZero.ne n))) h2
  rw [← ZMod.val_one_eq_one_mod] at h3
  exact Units.ext (ZMod.val_injective n h3)

/- English proof (translation)
Establish `: NeZero n` using `⟨hn.ne'⟩`. Establish `hrho : ∀ g x, charRep (cycK p K n) g x = x` using `fun g x => by`. Rewrite using `[charRep_apply, cycK_eq_one hμ, Units.val_one, one_mul]`. Take `⟨e⟩` from `h1_roots_of_unity_equiv_units_quot_pow p K n`. Establish `hbot : (Bd1 (charRep (cycK p K n))).comap (Z1 (charRep (cycK p K n))).subtype = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce `f hf`. Take `⟨m, hm⟩` from `(mem_contCoboundaries1 _ _).1 (Submodule.mem_comap.1 hf)`. Rewrite using `[Submodule.mem_bot]`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations.

Use `hm g` as an intermediate fact. Rewrite `this` using `[hrho, sub_self]`. Conclude with `this`. Set `Φ : Z1 (charRep (cycK p K n)) → {χ : charGrp (GK p K) // n • χ = 0}` to `fun f => ⟨⟨AddMonoidHom.mk' (fun a : Additive (GK p K) => zmodToQZ n (f.1 a.toMul)) fun a b => by show zmodToQZ n (f.1 (a.toMul * b.toMul)) = _`. Rewrite using `[f.2.2, hrho, map_add],`.

Use the proof step `((IsLocallyConstant.iff_continuous _).2 f.2.1).comp (zmodToQZ n)⟩,`. Use the proof step `Subtype.ext (AddMonoidHom.ext fun a => by show n • zmodToQZ n (f.1 a.toMul) = 0`. Rewrite using `[← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero])⟩`. Establish `hΦ : Bijective Φ`. Prove the components needed by the constructor for the conclusion.

Introduce `f f' h`. Use `Subtype.ext (funext fun g => zmodToQZ_injective n ?_)` and prove the remaining obligations. Conclude with `congrArg (fun χ : {χ : charGrp (GK p K) // n • χ = 0} => χ.1.1 (Additive.ofMul g)) h`. Introduce and unpack `⟨χ, hχ⟩`. Establish `hex : ∀ g : GK p K, ∃ a, zmodToQZ n a = χ.1 (Additive.ofMul g)` using `fun g => exists_zmodToQZ_eq n _ (congrArg (fun ψ : charGrp (GK p K) => ψ.1 (Additive.ofMul g)) hχ)`.

Use `choose f hf using hex`. Establish `hlc : IsLocallyConstant f`. Use `IsLocallyConstant.desc f (zmodToQZ n) ?_ (zmodToQZ_injective n)` and prove the remaining obligations. Establish `: zmodToQZ n ∘ f = fun g : GK p K => χ.1 (Additive.ofMul g)` using `funext hf`. Rewrite using `[this]`.

Conclude with `χ.2`. Use `⟨⟨f, hlc.continuous, fun g h => zmodToQZ_injective n ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hrho, map_add, hf, hf, hf]`. Conclude with `map_add χ.1 (Additive.ofMul g) (Additive.ofMul h)`. Conclude with `Subtype.ext (Subtype.ext (AddMonoidHom.ext fun a => hf a.toMul))`.

Rewrite using `[← Nat.card_congr (Equiv.ofBijective Φ hΦ), ← Nat.card_congr (Submodule.quotEquivOfEqBot _ hbot).toEquiv, Nat.card_congr e.toEquiv]`. Both sides reduce to the same expression.
-/
theorem card_character_n_torsion {n : ℕ} (hn : 0 < n) (hμ : ∀ ζ : PadicAlgCl p, ζ ^ n = 1 → ζ ∈ K) :
    Nat.card {χ : charGrp (GK p K) // n • χ = 0} = (powMonoidHom n : Kˣ →* Kˣ).range.index := by
  have : NeZero n := ⟨hn.ne'⟩
  have hrho : ∀ g x, charRep (cycK p K n) g x = x := fun g x => by
    rw [charRep_apply, cycK_eq_one hμ, Units.val_one, one_mul]
  obtain ⟨e⟩ := h1_roots_of_unity_equiv_units_quot_pow p K n
  have hbot : (Bd1 (charRep (cycK p K n))).comap (Z1 (charRep (cycK p K n))).subtype = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    obtain ⟨m, hm⟩ := (mem_contCoboundaries1 _ _).1 (Submodule.mem_comap.1 hf)
    rw [Submodule.mem_bot]
    refine Subtype.ext (funext fun g => ?_)
    have := hm g
    rw [hrho, sub_self] at this
    exact this
  let Φ : Z1 (charRep (cycK p K n)) → {χ : charGrp (GK p K) // n • χ = 0} := fun f =>
    ⟨⟨AddMonoidHom.mk' (fun a : Additive (GK p K) => zmodToQZ n (f.1 a.toMul)) fun a b => by
        show zmodToQZ n (f.1 (a.toMul * b.toMul)) = _
        rw [f.2.2, hrho, map_add],
      ((IsLocallyConstant.iff_continuous _).2 f.2.1).comp (zmodToQZ n)⟩,
     Subtype.ext (AddMonoidHom.ext fun a => by
        show n • zmodToQZ n (f.1 a.toMul) = 0
        rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero])⟩
  have hΦ : Bijective Φ := by
    constructor
    · intro f f' h
      refine Subtype.ext (funext fun g => zmodToQZ_injective n ?_)
      exact congrArg (fun χ : {χ : charGrp (GK p K) // n • χ = 0} => χ.1.1 (Additive.ofMul g)) h
    · rintro ⟨χ, hχ⟩
      have hex : ∀ g : GK p K, ∃ a, zmodToQZ n a = χ.1 (Additive.ofMul g) := fun g =>
        exists_zmodToQZ_eq n _ (congrArg (fun ψ : charGrp (GK p K) => ψ.1 (Additive.ofMul g)) hχ)
      choose f hf using hex
      have hlc : IsLocallyConstant f := by
        refine IsLocallyConstant.desc f (zmodToQZ n) ?_ (zmodToQZ_injective n)
        have : zmodToQZ n ∘ f = fun g : GK p K => χ.1 (Additive.ofMul g) := funext hf
        rw [this]
        exact χ.2
      refine ⟨⟨f, hlc.continuous, fun g h => zmodToQZ_injective n ?_⟩, ?_⟩
      · rw [hrho, map_add, hf, hf, hf]
        exact map_add χ.1 (Additive.ofMul g) (Additive.ofMul h)
      · exact Subtype.ext (Subtype.ext (AddMonoidHom.ext fun a => hf a.toMul))
  rw [← Nat.card_congr (Equiv.ofBijective Φ hΦ), ← Nat.card_congr (Submodule.quotEquivOfEqBot _ hbot).toEquiv,
    Nat.card_congr e.toEquiv]
  rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField
