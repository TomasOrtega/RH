import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj17.Pl :
    Type :=
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)

/- English proof (translation)
Introduce `v n`. Proceed by induction on `n using Nat.recOnMul with`. Consider the case `zero => intro h`. Conclude with `absurd rfl h`. Consider the case `one`.

Introduce `_ h`. Rewrite `h` using `[Nat.cast_one]`. Conclude with `absurd ((Ideal.eq_top_iff_one _).2 h) v.isPrime.ne_top`. Consider the case `prime p hp => intro _ h`. Conclude with `⟨p, hp, dvd_rfl, h⟩`.

Consider the case `mul a b iha ihb`. Introduce `h0 h`. Rewrite `h` using `[Nat.cast_mul]`. Break down `v.isPrime.mem_or_mem h with h | h` into its components or cases. Take `⟨p, hp, hd, hm⟩` from `iha (left_ne_zero_of_mul h0) h`.

Conclude with `⟨p, hp, hd.mul_right b, hm⟩`. Take `⟨p, hp, hd, hm⟩` from `ihb (right_ne_zero_of_mul h0) h`. Conclude with `⟨p, hp, hd.mul_left a, hm⟩`.
-/
theorem UpperTheory.Reformulated.B.Qj17.ho_exists_prime :
    ∀ (v : UpperTheory.Reformulated.B.Qj17.Pl) (n : ℕ),
      n ≠ (0 : ℕ) →
        (↑n : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal →
          ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal := by
  intro v n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    rw [Nat.cast_one] at h
    exact absurd ((Ideal.eq_top_iff_one _).2 h) v.isPrime.ne_top
  | prime p hp => intro _ h; exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b iha ihb =>
    intro h0 h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with h | h
    · obtain ⟨p, hp, hd, hm⟩ := iha (left_ne_zero_of_mul h0) h
      exact ⟨p, hp, hd.mul_right b, hm⟩
    · obtain ⟨p, hp, hd, hm⟩ := ihb (right_ne_zero_of_mul h0) h
      exact ⟨p, hp, hd.mul_left a, hm⟩
