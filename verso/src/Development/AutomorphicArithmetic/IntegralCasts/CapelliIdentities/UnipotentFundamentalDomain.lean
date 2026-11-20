import Mathlib

/- English proof (translation)
Introduce `K _ _ hn P Q hPQ hunder`. Establish `hPm : P.asIdeal.IsMaximal` using `P.isMaximal`. Establish `hQm : Q.asIdeal.IsMaximal` using `Q.isMaximal`. Establish `hne : P.asIdeal ≠ Q.asIdeal` using `fun h => hPQ (IsDedekindDomain.HeightOneSpectrum.ext h)`. Establish `hIprime : (Ideal.under ℤ P.asIdeal).IsPrime` using `Ideal.IsPrime.under ℤ P.asIdeal`.

Establish `hNP0 : Ideal.absNorm P.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `P.ne_bot`. Establish `hNmem : ((Ideal.absNorm P.asIdeal : ℕ) : ℤ) ∈ Ideal.under ℤ P.asIdeal`. Use `Ideal.absNorm_mem P.asIdeal` as an intermediate fact.

Simplify `this` using `[Ideal.under_def, Ideal.mem_comap]`. Take `⟨g, hg⟩` from `(IsPrincipalIdealRing.principal (Ideal.under ℤ P.asIdeal)).principal`. Establish `hg' : Ideal.under ℤ P.asIdeal = Ideal.span {g}` using `hg`. Establish `hg0 : g ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hNmem` using `[hg', Ideal.mem_span_singleton]`. Conclude with `hNP0 (by simpa using hNmem)`. Establish `hgprime : Prime g`. Rewrite `hIprime` using `[hg']`. Conclude with `(Ideal.span_singleton_prime hg0).1 hIprime`.

Use `set p : ℕ := g.natAbs with hpdef`. Establish `hp : p.Prime` using `Int.prime_iff_natAbs_prime.1 hgprime`. Establish `hpI : (p : ℤ) ∈ Ideal.under ℤ P.asIdeal`. Rewrite using `[hg', Ideal.mem_span_singleton]`. Conclude with `Int.dvd_natAbs.2 dvd_rfl`.

Establish `hpP : (p : NumberField.RingOfIntegers K) ∈ P.asIdeal`. Simplify `hpI` using `[Ideal.under_def, Ideal.mem_comap]`. Establish `hpQ : (p : NumberField.RingOfIntegers K) ∈ Q.asIdeal`. Rewrite `hpI` using `[hunder]`. Simplify `hpI` using `[Ideal.under_def, Ideal.mem_comap]`.

Establish `hnorm : Ideal.absNorm (Ideal.span {(p : NumberField.RingOfIntegers K)}) = p ^ Module.finrank ℚ K`. Establish `h : (p : NumberField.RingOfIntegers K) = algebraMap ℤ (NumberField.RingOfIntegers K) (p : ℤ)` using `by simp`. Rewrite using `[Ideal.absNorm_span_singleton, h, Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast, NumberField.RingOfIntegers.rank]`. Establish `hdvd : P.asIdeal * Q.asIdeal ∣ Ideal.span {(p : NumberField.RingOfIntegers K)}`. Rewrite using `[Ideal.dvd_iff_le, Ideal.mul_eq_inf_of_coprime (hPm.coprime_of_ne hQm hne)]`.

Conclude with `le_inf ((Ideal.span_singleton_le_iff_mem _).2 hpP) ((Ideal.span_singleton_le_iff_mem _).2 hpQ)`. Take `⟨J, hJ⟩` from `hdvd`. Establish `hprod : p ^ Module.finrank ℚ K = Ideal.absNorm P.asIdeal * Ideal.absNorm Q.asIdeal * Ideal.absNorm J`. Rewrite using `[← hnorm, hJ, map_mul, map_mul]`. Take `⟨a, -, ha⟩` from `(Nat.dvd_prime_pow hp).1 (Dvd.intro _ (by rw [hprod, mul_assoc]) : Ideal.absNorm P.asIdeal ∣ p ^ Module.finrank ℚ K)`.

Take `⟨b, -, hb⟩` from `(Nat.dvd_prime_pow hp).1 (Dvd.intro _ (by rw [hprod, mul_comm (Ideal.absNorm P.asIdeal), mul_assoc]) : Ideal.absNorm Q.asIdeal ∣ p ^ Module.finrank ℚ K)`. Take `⟨c, -, hc⟩` from `(Nat.dvd_prime_pow hp).1 (Dvd.intro_left _ hprod.symm : Ideal.absNorm J ∣ p ^ Module.finrank ℚ K)`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Rewrite `ha` using `[pow_zero, Ideal.absNorm_eq_one_iff]`.

Conclude with `hPm.ne_top ha`. Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Rewrite `hb` using `[pow_zero, Ideal.absNorm_eq_one_iff]`. Conclude with `hQm.ne_top hb`.

Establish `hexp : Module.finrank ℚ K = a + b + c`. Apply `Nat.pow_right_injective hp.two_le` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[hprod, ha, hb, hc, pow_add, pow_add]`. Establish `ha1 : a = 1` using `by omega`.

Establish `hc0 : c = 0` using `by omega`. Establish `hNP : Ideal.absNorm P.asIdeal = p` using `by rw [ha, ha1, pow_one]`. Establish `hJtop : J = ⊤`. Rewrite using `[← Ideal.absNorm_eq_one_iff, hc, hc0, pow_zero]`. Establish `hspan : Ideal.span {(p : NumberField.RingOfIntegers K)} = P.asIdeal * Q.asIdeal`.

Rewrite using `[hJ, hJtop, Ideal.mul_top]`. Establish `hp0 : (p : NumberField.RingOfIntegers K) ≠ 0`. Introduce `h`. Rewrite `hnorm` using `[h]`. Rewrite `hnorm` using `[Set.singleton_zero, Ideal.span_zero, Ideal.absNorm_bot]`.

Conclude with `pow_ne_zero _ hp.ne_zero hnorm.symm`. Establish `h1 : P.intValuation (p : NumberField.RingOfIntegers K) ≤ WithZero.exp (-((1 : ℕ) : ℤ))`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, hspan, pow_one]`. Conclude with `Dvd.intro _ rfl`. Establish `h2 : ¬ P.intValuation (p : NumberField.RingOfIntegers K) ≤ WithZero.exp (-((2 : ℕ) : ℤ))`.

Rewrite using `[IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, hspan, pow_two]`. Introduce `h`. Establish `h3 : P.asIdeal ∣ Q.asIdeal` using `(mul_dvd_mul_iff_left P.ne_bot).1 h`. Conclude with `hne (hQm.eq_of_le hPm.ne_top (Ideal.dvd_iff_le.1 h3)).symm`. Establish `hval : P.intValuation (p : NumberField.RingOfIntegers K) = WithZero.exp (-1 : ℤ)`.

Rewrite `h1`, `h2`, the goal using `[IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hp0]`. Rewrite `h1`, `h2` using `[WithZero.exp_le_exp]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hNP]`.

Establish `key` using `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := K) P (p : NumberField.RingOfIntegers K)`. Rewrite `key` using `[IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hval]`. Simplify using `using key`.
-/
theorem UpperTheory.Reformulated.B.UnipotentFundamentalDomain.val_two :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K],
    Module.finrank ℚ K ≤ (2 : ℕ) →
      ∀ (P Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        P ≠ Q →
          Ideal.under ℤ P.asIdeal = Ideal.under ℤ Q.asIdeal →
            (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion K P → WithZero (Multiplicative ℤ))
                (↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers K) → ℕ) P.asIdeal) :
                  IsDedekindDomain.HeightOneSpectrum.adicCompletion K P) =
              WithZero.exp (-1 : ℤ) := by
  intro K _ _ hn P Q hPQ hunder
  have hPm : P.asIdeal.IsMaximal := P.isMaximal
  have hQm : Q.asIdeal.IsMaximal := Q.isMaximal
  have hne : P.asIdeal ≠ Q.asIdeal := fun h => hPQ (IsDedekindDomain.HeightOneSpectrum.ext h)
  have hIprime : (Ideal.under ℤ P.asIdeal).IsPrime := Ideal.IsPrime.under ℤ P.asIdeal
  have hNP0 : Ideal.absNorm P.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.ne_bot
  have hNmem : ((Ideal.absNorm P.asIdeal : ℕ) : ℤ) ∈ Ideal.under ℤ P.asIdeal := by
    have := Ideal.absNorm_mem P.asIdeal
    simpa [Ideal.under_def, Ideal.mem_comap] using this
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (Ideal.under ℤ P.asIdeal)).principal
  have hg' : Ideal.under ℤ P.asIdeal = Ideal.span {g} := hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [hg', Ideal.mem_span_singleton] at hNmem
    exact hNP0 (by simpa using hNmem)
  have hgprime : Prime g := by
    rw [hg'] at hIprime
    exact (Ideal.span_singleton_prime hg0).1 hIprime
  set p : ℕ := g.natAbs with hpdef
  have hp : p.Prime := Int.prime_iff_natAbs_prime.1 hgprime
  have hpI : (p : ℤ) ∈ Ideal.under ℤ P.asIdeal := by
    rw [hg', Ideal.mem_span_singleton]
    exact Int.dvd_natAbs.2 dvd_rfl
  have hpP : (p : NumberField.RingOfIntegers K) ∈ P.asIdeal := by
    simpa [Ideal.under_def, Ideal.mem_comap] using hpI
  have hpQ : (p : NumberField.RingOfIntegers K) ∈ Q.asIdeal := by
    rw [hunder] at hpI
    simpa [Ideal.under_def, Ideal.mem_comap] using hpI
  have hnorm : Ideal.absNorm (Ideal.span {(p : NumberField.RingOfIntegers K)}) =
      p ^ Module.finrank ℚ K := by
    have h : (p : NumberField.RingOfIntegers K) =
        algebraMap ℤ (NumberField.RingOfIntegers K) (p : ℤ) := by simp
    rw [Ideal.absNorm_span_singleton, h, Algebra.norm_algebraMap, Int.natAbs_pow,
      Int.natAbs_natCast, NumberField.RingOfIntegers.rank]
  have hdvd : P.asIdeal * Q.asIdeal ∣ Ideal.span {(p : NumberField.RingOfIntegers K)} := by
    rw [Ideal.dvd_iff_le, Ideal.mul_eq_inf_of_coprime (hPm.coprime_of_ne hQm hne)]
    exact le_inf ((Ideal.span_singleton_le_iff_mem _).2 hpP)
      ((Ideal.span_singleton_le_iff_mem _).2 hpQ)
  obtain ⟨J, hJ⟩ := hdvd
  have hprod : p ^ Module.finrank ℚ K =
      Ideal.absNorm P.asIdeal * Ideal.absNorm Q.asIdeal * Ideal.absNorm J := by
    rw [← hnorm, hJ, map_mul, map_mul]
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).1
    (Dvd.intro _ (by rw [hprod, mul_assoc]) : Ideal.absNorm P.asIdeal ∣ p ^ Module.finrank ℚ K)
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).1
    (Dvd.intro _ (by rw [hprod, mul_comm (Ideal.absNorm P.asIdeal), mul_assoc]) :
      Ideal.absNorm Q.asIdeal ∣ p ^ Module.finrank ℚ K)
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).1
    (Dvd.intro_left _ hprod.symm : Ideal.absNorm J ∣ p ^ Module.finrank ℚ K)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.absNorm_eq_one_iff] at ha
    exact hPm.ne_top ha
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.absNorm_eq_one_iff] at hb
    exact hQm.ne_top hb
  have hexp : Module.finrank ℚ K = a + b + c := by
    apply Nat.pow_right_injective hp.two_le
    simp only
    rw [hprod, ha, hb, hc, pow_add, pow_add]
  have ha1 : a = 1 := by omega
  have hc0 : c = 0 := by omega
  have hNP : Ideal.absNorm P.asIdeal = p := by rw [ha, ha1, pow_one]
  have hJtop : J = ⊤ := by
    rw [← Ideal.absNorm_eq_one_iff, hc, hc0, pow_zero]
  have hspan : Ideal.span {(p : NumberField.RingOfIntegers K)} = P.asIdeal * Q.asIdeal := by
    rw [hJ, hJtop, Ideal.mul_top]
  have hp0 : (p : NumberField.RingOfIntegers K) ≠ 0 := by
    intro h
    rw [h] at hnorm
    rw [Set.singleton_zero, Ideal.span_zero, Ideal.absNorm_bot] at hnorm
    exact pow_ne_zero _ hp.ne_zero hnorm.symm
  have h1 : P.intValuation (p : NumberField.RingOfIntegers K) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, hspan, pow_one]
    exact Dvd.intro _ rfl
  have h2 : ¬ P.intValuation (p : NumberField.RingOfIntegers K) ≤
      WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, hspan, pow_two]
    intro h
    have h3 : P.asIdeal ∣ Q.asIdeal := (mul_dvd_mul_iff_left P.ne_bot).1 h
    exact hne (hQm.eq_of_le hPm.ne_top (Ideal.dvd_iff_le.1 h3)).symm
  have hval : P.intValuation (p : NumberField.RingOfIntegers K) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hp0] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1 h2
    congr 1
    omega
  rw [hNP]
  have key := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := K) P
    (p : NumberField.RingOfIntegers K)
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hval] at key
  simpa using key
