import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.FieldDisc
open NumberField
open scoped TensorProduct NNReal

open scoped Pointwise in
/- English proof (translation)
Establish `hsm : ∀ (σ : Gal(E/ℚ)) {x : 𝓞 E}, x ∈ differentIdeal ℤ (𝓞 E) → σ • x ∈ differentIdeal ℤ (𝓞 E)`. Introduce `σ x hx`. Use `Ideal.smul_mem_pointwise_smul σ x _ hx` as an intermediate fact. Rewrite `this` using `[KStar.Ram.smul_differentIdeal E σ]`. Then use the resulting hypothesis. Use `set D := differentIdeal ℤ (𝓞 E) with hD`.

Establish `hN : Ideal.absNorm D = (discr E).natAbs` using `absNorm_differentIdeal E (𝓞 E)`. Establish `hrel : Ideal.relNorm ℤ D = Ideal.span {discr E}`. Rewrite using `[Ideal.relNorm_int, hN, Ideal.span_singleton_eq_span_singleton]`. Conclude with `(Int.associated_natAbs _).symm`. Establish `hle : (Ideal.span {discr E}).map (algebraMap ℤ (𝓞 E)) ≤ D ^ Module.finrank ℚ E`.

Rewrite using `[← hrel, Ideal.map_le_iff_le_comap, Ideal.relNorm_apply, Ideal.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `h1 : algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) x) = ∏ σ : Gal(E/ℚ), σ • x`. Apply `FaithfulSMul.algebraMap_injective (𝓞 E) E` to reduce the goal to its premises. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ ℚ E, Algebra.algebraMap_intNorm (L := E), Algebra.norm_eq_prod_automorphisms, map_prod]`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) x) ∈ D ^ Module.finrank ℚ E`. Rewrite using `[h1, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card, ← Finset.card_univ, ← Finset.prod_const]`. Conclude with `Ideal.prod_mem_prod fun σ _ => hsm σ hx`. Take `⟨L, hL⟩` from `Ideal.dvd_iff_le.mpr hle`.

Establish `h2` using `congrArg Ideal.absNorm hL`. Rewrite `h2` using `[Ideal.absNorm_algebraMap, map_mul, map_pow, hN, RingOfIntegers.rank, Ideal.absNorm_span_singleton, Algebra.norm_self]`. Establish `h0 : (discr E).natAbs ^ Module.finrank ℚ E ≠ 0` using `pow_ne_zero _ (Int.natAbs_ne_zero.mpr (discr_ne_zero E))`. Establish `h3 : Ideal.absNorm L = 1`. Apply `mul_left_cancel₀ h0` to reduce the goal to its premises.

Rewrite using `[mul_one]`. Conclude with `h2.symm`. Rewrite using `[hL, Ideal.absNorm_eq_one_iff.mp h3, Ideal.mul_top]`.
-/
private theorem differentIdeal_pow_finrank_eq_discr (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] :
    differentIdeal ℤ (𝓞 E) ^ Module.finrank ℚ E =
      (Ideal.span {discr E}).map (algebraMap ℤ (𝓞 E)) := by
  classical
  have hsm : ∀ (σ : Gal(E/ℚ)) {x : 𝓞 E}, x ∈ differentIdeal ℤ (𝓞 E) →
      σ • x ∈ differentIdeal ℤ (𝓞 E) := by
    intro σ x hx
    have := Ideal.smul_mem_pointwise_smul σ x _ hx
    rwa [KStar.Ram.smul_differentIdeal E σ] at this
  set D := differentIdeal ℤ (𝓞 E) with hD
  have hN : Ideal.absNorm D = (discr E).natAbs := absNorm_differentIdeal E (𝓞 E)
  have hrel : Ideal.relNorm ℤ D = Ideal.span {discr E} := by
    rw [Ideal.relNorm_int, hN, Ideal.span_singleton_eq_span_singleton]
    exact (Int.associated_natAbs _).symm
  have hle : (Ideal.span {discr E}).map (algebraMap ℤ (𝓞 E)) ≤ D ^ Module.finrank ℚ E := by
    rw [← hrel, Ideal.map_le_iff_le_comap, Ideal.relNorm_apply, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h1 : algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) x) = ∏ σ : Gal(E/ℚ), σ • x := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ ℚ E,
        Algebra.algebraMap_intNorm (L := E), Algebra.norm_eq_prod_automorphisms, map_prod]
      rfl
    change algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) x) ∈ D ^ Module.finrank ℚ E
    rw [h1, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card, ← Finset.card_univ,
      ← Finset.prod_const]
    exact Ideal.prod_mem_prod fun σ _ => hsm σ hx
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.mpr hle
  have h2 := congrArg Ideal.absNorm hL
  rw [Ideal.absNorm_algebraMap, map_mul, map_pow, hN, RingOfIntegers.rank,
    Ideal.absNorm_span_singleton, Algebra.norm_self] at h2
  have h0 : (discr E).natAbs ^ Module.finrank ℚ E ≠ 0 :=
    pow_ne_zero _ (Int.natAbs_ne_zero.mpr (discr_ne_zero E))
  have h3 : Ideal.absNorm L = 1 := by
    apply mul_left_cancel₀ h0
    rw [mul_one]
    exact h2.symm
  rw [hL, Ideal.absNorm_eq_one_iff.mp h3, Ideal.mul_top]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hlt : w (m : R) < 1` using `lt_of_le_of_ne (hw _) hne`. Establish `hc : IsCoprime (p : R) (m : R)` using `Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)`. Take `⟨a, b, hab⟩` from `hc`. Establish `h1 : w (a * (p : R)) < 1`.

Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hw a)) hv`. Establish `h2 : w (b * (m : R)) < 1`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hw b)) hlt`.

Use `w.map_add_lt h1 h2` as an intermediate fact. Rewrite `this` using `[hab, map_one]`. Conclude with `lt_irrefl _ this`.
-/
private theorem val_nat_eq_one {R : Type} [CommRing R] (w : Valuation R ℝ≥0)
    (hw : ∀ x, w x ≤ 1) {p : ℕ} (hp : p.Prime) (hv : w (p : R) < 1) {m : ℕ} (hm : ¬ p ∣ m) :
    w (m : R) = 1 := by
  by_contra hne
  have hlt : w (m : R) < 1 := lt_of_le_of_ne (hw _) hne
  have hc : IsCoprime (p : R) (m : R) :=
    Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : w (a * (p : R)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hw a)) hv
  have h2 : w (b * (m : R)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hw b)) hlt
  have := w.map_add_lt h1 h2
  rw [hab, map_one] at this
  exact lt_irrefl _ this

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro x _`. Simplify using `using hw x`. Consider the case `succ n ih`. Introduce `x hx`.

Rewrite `hx` using `[pow_succ]`. Use `Submodule.mul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb`. Rewrite using `[map_mul, pow_succ]`. Conclude with `mul_le_mul' (ih a ha) (h b hb)`.

Introduce `a b ha hb`. Conclude with `w.map_add_le ha hb`.
-/
private theorem val_pow_le {R : Type} [CommRing R] (w : Valuation R ℝ≥0) (I : Ideal R) (c : ℝ≥0)
    (h : ∀ a ∈ I, w a ≤ c) (hw : ∀ x, w x ≤ 1) (n : ℕ) : ∀ x ∈ I ^ n, w x ≤ c ^ n := by
  induction n with
  | zero => intro x _; simpa using hw x
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [map_mul, pow_succ]
      exact mul_le_mul' (ih a ha) (h b hb)
    · intro a b ha hb
      exact w.map_add_le ha hb

/- English proof (translation)
Introduce `E _ _ _ p hp d m hd hm hdiv C _ v hv φ`. Set `ψ : 𝓞 E →+* C` to `φ.comp (algebraMap (𝓞 E) E)`. Set `w : Valuation (𝓞 E) ℝ≥0` to `v.comap ψ`. Establish `hwa : ∀ x, w x = v (ψ x)` using `fun x => rfl`. Establish `hw : ∀ x, w x ≤ 1`.

Introduce `x`. Establish `hi : IsIntegral ℤ (ψ x)` using `map_isIntegral_int ψ (Algebra.IsIntegral.isIntegral x)`. Establish `hi' : IsIntegral v.integer (ψ x)` using `hi.tower_top`. Conclude with `(Valuation.integer.integers v).mem_of_integral hi'`. Establish `hwp : w (p : 𝓞 E) = v (p : C)` using `by rw [hwa, map_natCast]`.

Establish `hdvd : ∀ a b : 𝓞 E, a ∣ b → w b ≤ w a`. Introduce and unpack `a _ ⟨c, rfl⟩`. Rewrite using `[map_mul]`. Conclude with `mul_le_of_le_one_right zero_le (hw c)`. Establish `hv' : w (p : 𝓞 E) < 1` using `hwp ▸ hv`.

Establish `hN0 : (discr E).natAbs ≠ 0` using `Int.natAbs_ne_zero.mpr (discr_ne_zero E)`. Establish `hdisc : w ((discr E : ℤ) : 𝓞 E) = v (p : C) ^ padicValNat p (discr E).natAbs`. Establish `h1 : w ((discr E : ℤ) : 𝓞 E) = w (((discr E).natAbs : ℕ) : 𝓞 E)`. Break down `Int.natAbs_eq (discr E) with h | h` into its components or cases. Use `conv_lhs => rw [h]`.

Rewrite using `[Int.cast_natCast]`. Use `conv_lhs => rw [h]`. Rewrite using `[Int.cast_neg, Int.cast_natCast, Valuation.map_neg]`. Take `⟨k, m', hm', hk⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hN0 p hp.ne_one`. Use `haveI : Fact p.Prime := ⟨hp⟩`.

Establish `hm0 : m' ≠ 0` using `by rintro rfl; exact hm' (dvd_zero p)`. Establish `hval : padicValNat p (discr E).natAbs = k`. Rewrite using `[hk, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm', add_zero]`. Rewrite using `[h1, hval, hk, Nat.cast_mul, Nat.cast_pow, map_mul, map_pow, hwp, val_nat_eq_one w hw hp hv' hm', mul_one]`. Establish `hpow` using `differentIdeal_pow_finrank_eq_discr E`.

Rewrite `hpow` using `[Ideal.map_span, Set.image_singleton, eq_intCast]`. Express the relevant statement in the definitionally equal form `w d ^ _ = _`. Rewrite using `[← hdisc]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← map_pow]`.

Apply `hdvd` to reduce the goal to its premises. Rewrite using `[← Ideal.mem_span_singleton, ← hpow]`. Conclude with `Ideal.pow_mem_pow hd _`. Apply `val_pow_le w (differentIdeal ℤ (𝓞 E)) (w d) _ hw` to reduce the goal to its premises. Rewrite using `[hpow]`.

Conclude with `Ideal.mem_span_singleton_self _`. Introduce `a ha`. Use `hdvd _ _ (hdiv a ha)` as an intermediate fact. Rewrite `this` using `[map_mul, val_nat_eq_one w hw hp hv' hm, one_mul]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.WildB.valGen :
    ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ), p.Prime → ∀ (d : 𝓞 E) (m : ℕ), d ∈ differentIdeal ℤ (𝓞 E) → ¬ p ∣ m → (∀ a ∈ differentIdeal ℤ (𝓞 E), d ∣ (m : 𝓞 E) * a) → ∀ (C : Type) [Field C] (v : Valuation C ℝ≥0), v (p : C) < 1 → ∀ φ : E →+* C, v (φ (d : E)) ^ Module.finrank ℚ E = v (p : C) ^ padicValNat p (discr E).natAbs := by
  intro E _ _ _ p hp d m hd hm hdiv C _ v hv φ
  let ψ : 𝓞 E →+* C := φ.comp (algebraMap (𝓞 E) E)
  let w : Valuation (𝓞 E) ℝ≥0 := v.comap ψ
  have hwa : ∀ x, w x = v (ψ x) := fun x => rfl
  have hw : ∀ x, w x ≤ 1 := by
    intro x
    have hi : IsIntegral ℤ (ψ x) := map_isIntegral_int ψ (Algebra.IsIntegral.isIntegral x)
    have hi' : IsIntegral v.integer (ψ x) := hi.tower_top
    exact (Valuation.integer.integers v).mem_of_integral hi'
  have hwp : w (p : 𝓞 E) = v (p : C) := by rw [hwa, map_natCast]
  have hdvd : ∀ a b : 𝓞 E, a ∣ b → w b ≤ w a := by
    rintro a _ ⟨c, rfl⟩
    rw [map_mul]
    exact mul_le_of_le_one_right zero_le (hw c)
  have hv' : w (p : 𝓞 E) < 1 := hwp ▸ hv
  have hN0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have hdisc : w ((discr E : ℤ) : 𝓞 E) = v (p : C) ^ padicValNat p (discr E).natAbs := by
    have h1 : w ((discr E : ℤ) : 𝓞 E) = w (((discr E).natAbs : ℕ) : 𝓞 E) := by
      rcases Int.natAbs_eq (discr E) with h | h
      · conv_lhs => rw [h]
        rw [Int.cast_natCast]
      · conv_lhs => rw [h]
        rw [Int.cast_neg, Int.cast_natCast, Valuation.map_neg]
    obtain ⟨k, m', hm', hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 p hp.ne_one
    haveI : Fact p.Prime := ⟨hp⟩
    have hm0 : m' ≠ 0 := by rintro rfl; exact hm' (dvd_zero p)
    have hval : padicValNat p (discr E).natAbs = k := by
      rw [hk, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd hm', add_zero]
    rw [h1, hval, hk, Nat.cast_mul, Nat.cast_pow, map_mul, map_pow, hwp,
      val_nat_eq_one w hw hp hv' hm', mul_one]
  have hpow := differentIdeal_pow_finrank_eq_discr E
  rw [Ideal.map_span, Set.image_singleton, eq_intCast] at hpow
  change w d ^ _ = _
  rw [← hdisc]
  apply le_antisymm
  · rw [← map_pow]
    apply hdvd
    rw [← Ideal.mem_span_singleton, ← hpow]
    exact Ideal.pow_mem_pow hd _
  · apply val_pow_le w (differentIdeal ℤ (𝓞 E)) (w d) _ hw
    · rw [hpow]
      exact Ideal.mem_span_singleton_self _
    · intro a ha
      have := hdvd _ _ (hdiv a ha)
      rwa [map_mul, val_nat_eq_one w hw hp hv' hm, one_mul] at this
