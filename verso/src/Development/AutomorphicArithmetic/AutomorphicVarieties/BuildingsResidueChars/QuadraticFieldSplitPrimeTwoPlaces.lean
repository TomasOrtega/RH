import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.S2
open scoped Pointwise

/- English proof (translation)
Establish `hco : IsCoprime w.asIdeal w'.asIdeal`. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Conclude with `w.isMaximal.coprime_of_ne w'.isMaximal fun h => hne (HeightOneSpectrum.ext h)`. Establish `hd : w.asIdeal * w'.asIdeal ∣ Ideal.span {((p : ℕ) : 𝓞 K)}` using `hco.mul_dvd (Ideal.dvd_span_singleton.2 hw) (Ideal.dvd_span_singleton.2 hw')`. Take `⟨J, hJ⟩` from `hd`.

Establish `hn : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ 2`. Rewrite using `[Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]`. Establish `e` using `congrArg Ideal.absNorm hJ`. Rewrite `e` using `[hn, map_mul, map_mul]`. Establish `a1` using `NumberField.HeightOneSpectrum.one_lt_absNorm w`.

Establish `a2` using `NumberField.HeightOneSpectrum.one_lt_absNorm w'`. Generalize the expression as in `Ideal.absNorm w.asIdeal = a at *`. Generalize the expression as in `Ideal.absNorm w'.asIdeal = b at *`. Take `⟨i, -, rfl⟩` from `(Nat.dvd_prime_pow hp).1 (show a ∣ p ^ 2 from ⟨b * Ideal.absNorm J, by rw [e, mul_assoc]⟩)`. Take `⟨j, -, rfl⟩` from `(Nat.dvd_prime_pow hp).1 (show b ∣ p ^ 2 from ⟨p ^ i * Ideal.absNorm J, by rw [e]; ring⟩)`.

Take `⟨k, -, hk⟩` from `(Nat.dvd_prime_pow hp).1 (show Ideal.absNorm J ∣ p ^ 2 from ⟨p ^ i * p ^ j, by rw [e]; ring⟩)`. Rewrite `e` using `[hk, ← pow_add, ← pow_add]`. Establish `e2` using `Nat.pow_right_injective hp.two_le e`. Establish `i0 : i ≠ 0` using `by rintro rfl; simp at a1`. Establish `j0 : j ≠ 0` using `by rintro rfl; simp at a2`.

Establish `i1 : i = 1` using `by omega`. Establish `k0 : k = 0` using `by omega`. Rewrite `hk` using `[k0, pow_zero, Ideal.absNorm_eq_one_iff]`. Use `⟨by rw [i1, pow_one], ?_⟩` and prove the remaining obligations. Rewrite using `[hJ, hk, Ideal.mul_top]`.
-/
private theorem two_primes {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    {w w' : HeightOneSpectrum (𝓞 K)} (hne : w ≠ w') (hw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) (hw' : ((p : ℕ) : 𝓞 K) ∈ w'.asIdeal) :
    Ideal.absNorm w.asIdeal = p ∧ Ideal.span {((p : ℕ) : 𝓞 K)} = w.asIdeal * w'.asIdeal := by
  have hco : IsCoprime w.asIdeal w'.asIdeal := by
    rw [Ideal.isCoprime_iff_sup_eq]
    exact w.isMaximal.coprime_of_ne w'.isMaximal fun h => hne (HeightOneSpectrum.ext h)
  have hd : w.asIdeal * w'.asIdeal ∣ Ideal.span {((p : ℕ) : 𝓞 K)} :=
    hco.mul_dvd (Ideal.dvd_span_singleton.2 hw) (Ideal.dvd_span_singleton.2 hw')
  obtain ⟨J, hJ⟩ := hd
  have hn : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]
  have e := congrArg Ideal.absNorm hJ
  rw [hn, map_mul, map_mul] at e
  have a1 := NumberField.HeightOneSpectrum.one_lt_absNorm w
  have a2 := NumberField.HeightOneSpectrum.one_lt_absNorm w'
  generalize Ideal.absNorm w.asIdeal = a at *
  generalize Ideal.absNorm w'.asIdeal = b at *
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 (show a ∣ p ^ 2 from ⟨b * Ideal.absNorm J, by rw [e, mul_assoc]⟩)
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 (show b ∣ p ^ 2 from ⟨p ^ i * Ideal.absNorm J, by rw [e]; ring⟩)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 (show Ideal.absNorm J ∣ p ^ 2 from ⟨p ^ i * p ^ j, by rw [e]; ring⟩)
  rw [hk, ← pow_add, ← pow_add] at e
  have e2 := Nat.pow_right_injective hp.two_le e
  have i0 : i ≠ 0 := by rintro rfl; simp at a1
  have j0 : j ≠ 0 := by rintro rfl; simp at a2
  have i1 : i = 1 := by omega
  have k0 : k = 0 := by omega
  rw [k0, pow_zero, Ideal.absNorm_eq_one_iff] at hk
  refine ⟨by rw [i1, pow_one], ?_⟩
  rw [hJ, hk, Ideal.mul_top]

/- English proof (translation)
Rewrite `hu` using `[h]`. Break down `u.isPrime.mul_le.1 hu with h1 | h1` into its components or cases. Conclude with `Or.inl (HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top h1).symm)`. Conclude with `Or.inr (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le u.isPrime.ne_top h1).symm)`.
-/
private theorem only_two {K : Type} [Field K] [NumberField K] {I : Ideal (𝓞 K)}
    {w w' u : HeightOneSpectrum (𝓞 K)} (h : I = w.asIdeal * w'.asIdeal) (hu : I ≤ u.asIdeal) : u = w ∨ u = w' := by
  rw [h] at hu
  rcases u.isPrime.mul_le.1 hu with h1 | h1
  · exact Or.inl (HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top h1).symm)
  · exact Or.inr (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le u.isPrime.ne_top h1).symm)

/- English proof (translation)
Introduce `Ω _ _ _ k₀ _ h2 p hp hs`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : IsAlgClosure k₀ Ω := ⟨inferInstance, inferInstance⟩`.

Establish `key : ∀ A A' : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∀ g : G ℚ Ω, g ∉ k₀.fixingSubgroup → (∀ y, g y ∈ A ↔ y ∈ A') → ∃ w w' : Pl k₀, w ≠ w' ∧ ((p : ℕ) : 𝓞 k₀) ∈ w.asIdeal ∧ ((p : ℕ) : 𝓞 k₀) ∈ w'.asIdeal ∧ IsPlaceOver A w ∧ IsPlaceOver A' w'`. Introduce `A A' hA g hg hAA`. Establish `hA' : A'.valuation (p : Ω) < 1`. Rewrite `hA`, the goal using `[valuation_lt_one_iff']`. Rewrite using `[← hAA, ← hAA, map_inv₀, map_natCast]`.

Conclude with `hA`. Take `⟨a1, a2, a3, -⟩` from `places k₀ Ω p A`. Take `⟨b1, b2, b3, -⟩` from `places k₀ Ω p A'`. Take `⟨v, hv⟩` from `a1 fun h => (a2 h).2 hA`. Take `⟨u, hu⟩` from `b1 fun h => (b2 h).2 hA'`.

Use `⟨v, u, ?_, (a3 v hv).1 hA, (b3 u hu).1 hA', hv, hu⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Take `⟨h, hh⟩` from `exists_smul_eq_of_isPlaceOver hv hu`. Establish `hm : g * galEmb ℚ k₀ Ω h ∈ Dec (F` using `ℚ) A := by`. Establish `e : g • A' = A`.

Use extensionality with `y`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← hAA]`. Conclude with `iff_of_eq (congrArg (· ∈ A) (g.apply_symm_apply y))`. Use `show (g * galEmb ℚ k₀ Ω h) • A = A`. Rewrite using `[mul_smul, show galEmb ℚ k₀ Ω h • A = A' from hh, e]`.

Establish `hk : galEmb ℚ k₀ Ω h ∈ k₀.fixingSubgroup` using `(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => h.commutes ⟨x, hx⟩`. Conclude with `hg ((Subgroup.mul_mem_cancel_right _ hk).1 (hs A hA hm))`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g : G ℚ Ω, g ∉ k₀.fixingSubgroup := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Use `haveI : IsGalois ℚ Ω := {}`. Establish `e : k₀ = ⊥`. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup k₀, (Subgroup.eq_top_iff' _).2 hc, InfiniteGalois.fixedField_bot]`. Rewrite `h2` using `[IntermediateField.finrank_eq_one_iff.2 e]`. Use linear arithmetic over natural numbers and integers.

Establish `other : ∀ w : Pl k₀, ((p : ℕ) : 𝓞 k₀) ∈ w.asIdeal → ∃ w' : Pl k₀, w ≠ w' ∧ ((p : ℕ) : 𝓞 k₀) ∈ w'.asIdeal`. Introduce `w hw`. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω w`. Take `⟨v, u, hne, hv, hu, h1, -⟩` from `key A (A.comap g.toRingEquiv.toRingHom) (((places k₀ Ω p A).2.2.1 w hA).2 hw) g hg fun _ => Iff.rfl`. Establish `e : v = w` using `HeightOneSpectrum.ext (Ideal.ext fun x => (h1 x).symm.trans (hA x))`.

Conclude with `⟨u, e ▸ hne, hu⟩`. Use `⟨fun w hw => ?_, ?_⟩` and prove the remaining obligations. Take `⟨w', hne, hw'⟩` from `other w hw`. Take `⟨h1, h3⟩` from `two_primes h2 hp hne hw hw'`. Use `⟨h1, fun h => hne ?_⟩` and prove the remaining obligations.

Rewrite `h` using `[← Ideal.dvd_span_singleton, h3, sq, mul_dvd_mul_iff_left w.ne_bot, Ideal.dvd_iff_le]`. Conclude with `HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top h).symm`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w : Pl k₀, ((p : ℕ) : 𝓞 k₀) ∈ w.asIdeal := by`. Establish `hn : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 k₀)}) = p ^ 2`. Rewrite using `[Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]`.

Establish `ht : Ideal.span {((p : ℕ) : 𝓞 k₀)} ≠ ⊤` using `fun h => by`. Rewrite `hn` using `[Ideal.absNorm_eq_one_iff.2 h]`. Conclude with `(Nat.one_lt_pow two_ne_zero hp.one_lt).ne hn`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ ht`. Establish `hpM` using `(Ideal.span_singleton_le_iff_mem _).1 hle`.

Use `⟨⟨M, hM.isPrime, fun h => ?_⟩, hpM⟩` and prove the remaining obligations. Rewrite `hpM` using `[h, Ideal.mem_bot, Nat.cast_eq_zero]`. Conclude with `hp.ne_zero hpM`. Take `⟨w', hne, hw'⟩` from `other w hw`. Take `⟨-, h3⟩` from `two_primes h2 hp hne hw hw'`.

Use `⟨w, w', hne, hw, hw', fun A A' hA g hg hAA => ?_⟩` and prove the remaining obligations. Take `⟨v, u, hvu, hv, hu, h1, h4⟩` from `key A A' hA g hg hAA`. Apply the tactic sequence `rcases only_two h3 ((Ideal.span_singleton_le_iff_mem _).2 hv) with rfl | rfl <;>`. Break down `only_two h3 ((Ideal.span_singleton_le_iff_mem _).2 hu) with rfl | rfl` into its components or cases. Use `exacts [absurd rfl hvu, Or.inl ⟨h1, h4⟩, Or.inr ⟨h1, h4⟩, absurd rfl hvu]`.
-/
theorem UpperTheory.quadratic_field_split_prime_two_places :
    UpperTheory.V.Sd.S2.QuadSplit := by
  intro Ω _ _ _ k₀ _ h2 p hp hs
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure k₀ Ω := ⟨inferInstance, inferInstance⟩
  have key : ∀ A A' : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∀ g : G ℚ Ω, g ∉ k₀.fixingSubgroup →
      (∀ y, g y ∈ A ↔ y ∈ A') → ∃ w w' : Pl k₀, w ≠ w' ∧ ((p : ℕ) : 𝓞 k₀) ∈ w.asIdeal ∧ ((p : ℕ) : 𝓞 k₀) ∈ w'.asIdeal ∧
        IsPlaceOver A w ∧ IsPlaceOver A' w' := by
    intro A A' hA g hg hAA
    have hA' : A'.valuation (p : Ω) < 1 := by
      rw [valuation_lt_one_iff'] at hA ⊢
      rw [← hAA, ← hAA, map_inv₀, map_natCast]
      exact hA
    obtain ⟨a1, a2, a3, -⟩ := places k₀ Ω p A
    obtain ⟨b1, b2, b3, -⟩ := places k₀ Ω p A'
    obtain ⟨v, hv⟩ := a1 fun h => (a2 h).2 hA
    obtain ⟨u, hu⟩ := b1 fun h => (b2 h).2 hA'
    refine ⟨v, u, ?_, (a3 v hv).1 hA, (b3 u hu).1 hA', hv, hu⟩
    rintro rfl
    obtain ⟨h, hh⟩ := exists_smul_eq_of_isPlaceOver hv hu
    have hm : g * galEmb ℚ k₀ Ω h ∈ Dec (F := ℚ) A := by
      have e : g • A' = A := by
        ext y
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← hAA]
        exact iff_of_eq (congrArg (· ∈ A) (g.apply_symm_apply y))
      show (g * galEmb ℚ k₀ Ω h) • A = A
      rw [mul_smul, show galEmb ℚ k₀ Ω h • A = A' from hh, e]
    have hk : galEmb ℚ k₀ Ω h ∈ k₀.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => h.commutes ⟨x, hx⟩
    exact hg ((Subgroup.mul_mem_cancel_right _ hk).1 (hs A hA hm))
  obtain ⟨g, hg⟩ : ∃ g : G ℚ Ω, g ∉ k₀.fixingSubgroup := by
    by_contra hc
    push Not at hc
    haveI : IsGalois ℚ Ω := {}
    have e : k₀ = ⊥ := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup k₀, (Subgroup.eq_top_iff' _).2 hc, InfiniteGalois.fixedField_bot]
    rw [IntermediateField.finrank_eq_one_iff.2 e] at h2
    omega
  have other : ∀ w : Pl k₀, ((p : ℕ) : 𝓞 k₀) ∈ w.asIdeal → ∃ w' : Pl k₀, w ≠ w' ∧ ((p : ℕ) : 𝓞 k₀) ∈ w'.asIdeal := by
    intro w hw
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨v, u, hne, hv, hu, h1, -⟩ := key A (A.comap g.toRingEquiv.toRingHom)
      (((places k₀ Ω p A).2.2.1 w hA).2 hw) g hg fun _ => Iff.rfl
    have e : v = w := HeightOneSpectrum.ext (Ideal.ext fun x => (h1 x).symm.trans (hA x))
    exact ⟨u, e ▸ hne, hu⟩
  refine ⟨fun w hw => ?_, ?_⟩
  · obtain ⟨w', hne, hw'⟩ := other w hw
    obtain ⟨h1, h3⟩ := two_primes h2 hp hne hw hw'
    refine ⟨h1, fun h => hne ?_⟩
    rw [← Ideal.dvd_span_singleton, h3, sq, mul_dvd_mul_iff_left w.ne_bot, Ideal.dvd_iff_le] at h
    exact HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top h).symm
  · obtain ⟨w, hw⟩ : ∃ w : Pl k₀, ((p : ℕ) : 𝓞 k₀) ∈ w.asIdeal := by
      have hn : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 k₀)}) = p ^ 2 := by
        rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]
      have ht : Ideal.span {((p : ℕ) : 𝓞 k₀)} ≠ ⊤ := fun h => by
        rw [Ideal.absNorm_eq_one_iff.2 h] at hn
        exact (Nat.one_lt_pow two_ne_zero hp.one_lt).ne hn
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ ht
      have hpM := (Ideal.span_singleton_le_iff_mem _).1 hle
      refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, hpM⟩
      rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hpM
      exact hp.ne_zero hpM
    obtain ⟨w', hne, hw'⟩ := other w hw
    obtain ⟨-, h3⟩ := two_primes h2 hp hne hw hw'
    refine ⟨w, w', hne, hw, hw', fun A A' hA g hg hAA => ?_⟩
    obtain ⟨v, u, hvu, hv, hu, h1, h4⟩ := key A A' hA g hg hAA
    rcases only_two h3 ((Ideal.span_singleton_le_iff_mem _).2 hv) with rfl | rfl <;>
      rcases only_two h3 ((Ideal.span_singleton_le_iff_mem _).2 hu) with rfl | rfl
    exacts [absurd rfl hvu, Or.inl ⟨h1, h4⟩, Or.inr ⟨h1, h4⟩, absurd rfl hvu]
