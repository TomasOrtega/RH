import Mathlib

/- English proof (translation)
Introduce `v n`. Proceed by induction on `n using induction_on_primes with`. Consider the case `zero => intro h`. Conclude with `absurd rfl h`. Consider the case `one`.

Introduce `_ h`. Rewrite `h` using `[Nat.cast_one]`. Conclude with `absurd ((Ideal.eq_top_iff_one _).2 h) v.isPrime.ne_top`. Consider the case `prime_mul p a hp ih`. Introduce `h0 h`.

Rewrite `h` using `[Nat.cast_mul]`. Break down `v.isPrime.mem_or_mem h with h | h` into its components or cases. Conclude with `⟨p, hp, Dvd.intro _ rfl, h⟩`. Take `⟨q, hq, hqa, hqv⟩` from `ih (right_ne_zero_of_mul h0) h`. Conclude with `⟨q, hq, Dvd.dvd.mul_left hqa p, hqv⟩`.
-/
theorem UpperTheory.Reformulated.B.Qj5.df_exists_prime :
    ∀
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
    n ≠ (0 : ℕ) →
      (↑n : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal →
        ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal := by
  intro v n
  induction n using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    rw [Nat.cast_one] at h
    exact absurd ((Ideal.eq_top_iff_one _).2 h) v.isPrime.ne_top
  | prime_mul p a hp ih =>
    intro h0 h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with h | h
    · exact ⟨p, hp, Dvd.intro _ rfl, h⟩
    · obtain ⟨q, hq, hqa, hqv⟩ := ih (right_ne_zero_of_mul h0) h
      exact ⟨q, hq, Dvd.dvd.mul_left hqa p, hqv⟩
