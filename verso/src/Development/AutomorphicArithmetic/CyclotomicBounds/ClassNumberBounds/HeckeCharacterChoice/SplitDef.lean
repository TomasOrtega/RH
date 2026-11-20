import Mathlib

open NumberField

namespace KStar.Choice

def SplitsCompletely (E : Type*) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 E), P.IsPrime → P.LiesOver (Ideal.span {(p : ℤ)}) →
    P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1

/- English proof (translation)
The claim follows from `(Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)`.
-/
private theorem span_isPrime {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)

/- English proof (translation)
Use `span_isPrime hp` as an intermediate fact. Establish `: (Ideal.span {(p : ℤ)}).IsMaximal` using `Ideal.IsPrime.isMaximal this (by simpa using hp.ne_zero)`. Conclude with `IsDedekindDomain.primesOver_finite _ _`.
-/
private theorem primesOver_finite (E : Type*) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)).Finite := by
  have := span_isPrime hp
  have : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal this (by simpa using hp.ne_zero)
  exact IsDedekindDomain.primesOver_finite _ _

/- English proof (translation)
Use `span_isPrime hp` as an intermediate fact. Rewrite using `[Ideal.sum_ramification_inertia_eq_finrank, RingOfIntegers.rank]`.
-/
private theorem sum_ef (E : Type*) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    [Fintype ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E))] :
    ∑ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 E), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ =
      Module.finrank ℚ E := by
  have := span_isPrime hp
  rw [Ideal.sum_ramification_inertia_eq_finrank, RingOfIntegers.rank]

/- English proof (translation)
Use `q.2.1` as an intermediate fact. Conclude with `Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)`.
-/
private theorem one_le_ef (E : Type*) [Field E] [NumberField E] {p : ℕ}
    (q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 E)) :
    1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
  have := q.2.1
  exact Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)

/- English proof (translation)
Rewrite using `[← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]`. Simplify using the standard rewrite rules.
-/
private theorem ncard_eq_sum (E : Type*) [Field E] [NumberField E] {p : ℕ}
    [Fintype ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E))] :
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)).ncard =
      ∑ _q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 E), 1 := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  simp

/- English proof (translation)
Use `(primesOver_finite E hp).fintype` as an intermediate fact. Rewrite using `[ncard_eq_sum, ← sum_ef E hp]`. Conclude with `Finset.sum_le_sum fun q _ => one_le_ef E q`.
-/
private theorem ncard_le (E : Type*) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)).ncard ≤ Module.finrank ℚ E := by
  have := (primesOver_finite E hp).fintype
  rw [ncard_eq_sum, ← sum_ef E hp]
  exact Finset.sum_le_sum fun q _ => one_le_ef E q

/- English proof (translation)
Use `Fact.mk hp` as an intermediate fact. Establish `hinj : Function.Injective (fun φ : 𝓞 E →+* ZMod p => RingHom.ker φ)` using `fun φ ψ h => ZMod.ringHom_eq_of_ker_eq φ ψ h`. Rewrite using `[← Set.ncard_range_of_injective hinj]`. Use `congr 1`. Use extensionality with `P`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨φ, rfl⟩`. Establish `h1 : (RingHom.ker φ).IsPrime` using `RingHom.ker_isPrime φ`. Establish `h2 : (RingHom.ker φ).LiesOver (Ideal.span {(p : ℤ)})`. Use `⟨?_⟩` and prove the remaining obligations.

Rewrite using `[← ZMod.ker_intCastRingHom, Ideal.under_def, RingHom.comap_ker]`. Use `congr 1`. Conclude with `RingHom.ext_int _ _`. Use `⟨⟨h1, h2⟩, ?_⟩` and prove the remaining obligations. Establish `h3` using `Ideal.pow_inertiaDeg p (RingHom.ker φ)`.

Rewrite `h3` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective φ)).toEquiv, Nat.card_zmod]`. Conclude with `Nat.pow_right_injective hp.two_le (by simpa using h3)`. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Establish `h4` using `Ideal.pow_inertiaDeg p P`. Rewrite `h4` using `[h3, pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.

Establish `: Finite (𝓞 E ⧸ P)` using `Nat.finite_of_card_ne_zero (h4 ▸ hp.ne_zero)`. Use `Fintype.ofFinite (𝓞 E ⧸ P)` as an intermediate fact. Establish `e : ZMod p ≃+* (𝓞 E ⧸ P)` using `ZMod.ringEquivOfPrime (𝓞 E ⧸ P) hp (by rw [← Nat.card_eq_fintype_card, ← h4])`. Use `⟨e.symm.toRingHom.comp (Ideal.Quotient.mk P), ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Simplify using `[RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]`.
-/
private theorem card_hom_eq (E : Type*) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    Nat.card (𝓞 E →+* ZMod p) =
      {P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 E) | P.inertiaDeg ℤ = 1}.ncard := by
  have := Fact.mk hp
  have hinj : Function.Injective (fun φ : 𝓞 E →+* ZMod p => RingHom.ker φ) :=
    fun φ ψ h => ZMod.ringHom_eq_of_ker_eq φ ψ h
  rw [← Set.ncard_range_of_injective hinj]
  congr 1
  ext P
  constructor
  · rintro ⟨φ, rfl⟩
    have h1 : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    have h2 : (RingHom.ker φ).LiesOver (Ideal.span {(p : ℤ)}) := by
      refine ⟨?_⟩
      rw [← ZMod.ker_intCastRingHom, Ideal.under_def, RingHom.comap_ker]
      congr 1
      exact RingHom.ext_int _ _
    refine ⟨⟨h1, h2⟩, ?_⟩
    have h3 := Ideal.pow_inertiaDeg p (RingHom.ker φ)
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Nat.card_congr (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective φ)).toEquiv,
      Nat.card_zmod] at h3
    exact Nat.pow_right_injective hp.two_le (by simpa using h3)
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have h4 := Ideal.pow_inertiaDeg p P
    rw [h3, pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply] at h4
    have : Finite (𝓞 E ⧸ P) := Nat.finite_of_card_ne_zero (h4 ▸ hp.ne_zero)
    have := Fintype.ofFinite (𝓞 E ⧸ P)
    have e : ZMod p ≃+* (𝓞 E ⧸ P) :=
      ZMod.ringEquivOfPrime (𝓞 E ⧸ P) hp (by rw [← Nat.card_eq_fintype_card, ← h4])
    refine ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk P), ?_⟩
    ext x
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/- English proof (translation)
Use `(primesOver_finite E hp).fintype` as an intermediate fact. Rewrite using `[ncard_eq_sum, ← sum_ef E hp, Finset.sum_eq_sum_iff_of_le fun q _ => one_le_ef E q]`. Prove the components needed by the constructor for the conclusion. Introduce `h q _`. Take `⟨h1, h2⟩` from `h q.1 q.2.1 q.2.2`.

Rewrite using `[h1, h2]`. Introduce `h P h1 h2`. Use `h ⟨P, h1, h2⟩ (Finset.mem_univ _)` as an intermediate fact. Conclude with `⟨Nat.eq_one_of_mul_eq_one_right this.symm, Nat.eq_one_of_mul_eq_one_left this.symm⟩`.
-/
theorem splitsCompletely_iff_ncard (E : Type*) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    SplitsCompletely E p ↔
      ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E := by
  have := (primesOver_finite E hp).fintype
  rw [ncard_eq_sum, ← sum_ef E hp, Finset.sum_eq_sum_iff_of_le fun q _ => one_le_ef E q]
  constructor
  · intro h q _
    obtain ⟨h1, h2⟩ := h q.1 q.2.1 q.2.2
    rw [h1, h2]
  · intro h P h1 h2
    have := h ⟨P, h1, h2⟩ (Finset.mem_univ _)
    exact ⟨Nat.eq_one_of_mul_eq_one_right this.symm, Nat.eq_one_of_mul_eq_one_left this.symm⟩

/- English proof (translation)
Rewrite using `[card_hom_eq E hp]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← (splitsCompletely_iff_ncard E hp).1 h]`. Use `congr 1`.

Use extensionality with `P`. Conclude with `⟨fun h' => h'.1, fun h' => ⟨h', (h P h'.1 h'.2).2⟩⟩`. Introduce `h`. Use `(splitsCompletely_iff_ncard E hp).2 (le_antisymm (ncard_le E hp) ?_)` and prove the remaining obligations. Rewrite using `[← h]`.

Conclude with `Set.ncard_le_ncard (fun P hP => hP.1) (primesOver_finite E hp)`.
-/
theorem splitsCompletely_iff_card_hom (E : Type*) [Field E] [NumberField E] {p : ℕ}
    (hp : p.Prime) :
    SplitsCompletely E p ↔ Nat.card (𝓞 E →+* ZMod p) = Module.finrank ℚ E := by
  rw [card_hom_eq E hp]
  constructor
  · intro h
    rw [← (splitsCompletely_iff_ncard E hp).1 h]
    congr 1
    ext P
    exact ⟨fun h' => h'.1, fun h' => ⟨h', (h P h'.1 h'.2).2⟩⟩
  · intro h
    refine (splitsCompletely_iff_ncard E hp).2 (le_antisymm (ncard_le E hp) ?_)
    rw [← h]
    exact Set.ncard_le_ncard (fun P hP => hP.1) (primesOver_finite E hp)

/- English proof (translation)
Introduce `P h1 h2`. Establish `_` using `hp`. Take `⟨⟨Q, hQ1, hQ2⟩⟩` from `Ideal.nonempty_primesOver (S := 𝓞 L) P`. Establish `hQ3 : Q.LiesOver (Ideal.span {(p : ℤ)})` using `Ideal.LiesOver.trans Q P _`. Take `⟨h3, h4⟩` from `h Q hQ1 hQ3`.

Conclude with `⟨Nat.dvd_one.1 (h3 ▸ Ideal.ramificationIdx_below_dvd (R := ℤ) P Q), Nat.dvd_one.1 (h4 ▸ Ideal.inertiaDeg_below_dvd (R := ℤ) P Q)⟩`.
-/
theorem SplitsCompletely.of_tower {E L : Type*} [Field E] [NumberField E] [Field L]
    [NumberField L] [Algebra E L] {p : ℕ} (hp : p.Prime) (h : SplitsCompletely L p) :
    SplitsCompletely E p := by
  intro P h1 h2
  have _ := hp
  obtain ⟨⟨Q, hQ1, hQ2⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) P
  have hQ3 : Q.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans Q P _
  obtain ⟨h3, h4⟩ := h Q hQ1 hQ3
  exact ⟨Nat.dvd_one.1 (h3 ▸ Ideal.ramificationIdx_below_dvd (R := ℤ) P Q),
    Nat.dvd_one.1 (h4 ▸ Ideal.inertiaDeg_below_dvd (R := ℤ) P Q)⟩

end KStar.Choice
