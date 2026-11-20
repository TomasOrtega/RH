import Mathlib

/- English proof (translation)
Introduce `v p hp hmem`. Establish `hprime : Prime (p : NumberField.RingOfIntegers ℚ)`. Rewrite using `[← MulEquiv.prime_iff Rat.ringOfIntegersEquiv]`. Rewrite using `[map_natCast]`. Conclude with `Nat.prime_iff_prime_int.mp hp`.

Establish `hP : (Ideal.span {(p : NumberField.RingOfIntegers ℚ)}).IsPrime` using `(Ideal.span_singleton_prime hprime.ne_zero).mpr hprime`. Establish `hne : Ideal.span {(p : NumberField.RingOfIntegers ℚ)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hprime.ne_zero`. Establish `hmax : (Ideal.span {(p : NumberField.RingOfIntegers ℚ)}).IsMaximal` using `hP.isMaximal hne`.

Conclude with `(hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hmem)).symm`.
-/
theorem UpperTheory.Reformulated.B.Qi16.rayPrime_span :
    ∀
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (p : ℕ),
    Nat.Prime p →
      (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal → v.asIdeal = Ideal.span {(↑p : NumberField.RingOfIntegers ℚ)} := by
  intro v p hp hmem
  have hprime : Prime (p : NumberField.RingOfIntegers ℚ) := by
    rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv]
    rw [map_natCast]
    exact Nat.prime_iff_prime_int.mp hp
  have hP : (Ideal.span {(p : NumberField.RingOfIntegers ℚ)}).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hne : Ideal.span {(p : NumberField.RingOfIntegers ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hprime.ne_zero
  have hmax : (Ideal.span {(p : NumberField.RingOfIntegers ℚ)}).IsMaximal :=
    hP.isMaximal hne
  exact (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hmem)).symm
