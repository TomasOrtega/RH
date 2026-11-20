import Mathlib

/- English proof (translation)
Introduce `v n`. Proceed by induction on `n using Nat.recOnMul with`. Consider the case `zero => intro h`. Conclude with `absurd rfl h`. Consider the case `one`.

Introduce `_ h`. Conclude with `absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) v.isPrime.ne_top`. Consider the case `prime p hp => intro _ h`. Conclude with `⟨p, hp, dvd_rfl, h⟩`. Consider the case `mul a b iha ihb`.

Introduce `hab h`. Rewrite `h` using `[Nat.cast_mul]`. Break down `v.isPrime.mem_or_mem h with h | h` into its components or cases. Take `⟨p, hp, hd, hm⟩` from `iha (left_ne_zero_of_mul hab) h`. Conclude with `⟨p, hp, hd.mul_right _, hm⟩`.

Take `⟨p, hp, hd, hm⟩` from `ihb (right_ne_zero_of_mul hab) h`. Conclude with `⟨p, hp, hd.mul_left _, hm⟩`.
-/
theorem UpperTheory.Reformulated.B.Qk11.dz_exists_prime :
    ∀
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
    n ≠ (0 : ℕ) →
      (↑n : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal →
        ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal := by
  intro v n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    exact absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) v.isPrime.ne_top
  | prime p hp => intro _ h; exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b iha ihb =>
    intro hab h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with h | h
    · obtain ⟨p, hp, hd, hm⟩ := iha (left_ne_zero_of_mul hab) h
      exact ⟨p, hp, hd.mul_right _, hm⟩
    · obtain ⟨p, hp, hd, hm⟩ := ihb (right_ne_zero_of_mul hab) h
      exact ⟨p, hp, hd.mul_left _, hm⟩
