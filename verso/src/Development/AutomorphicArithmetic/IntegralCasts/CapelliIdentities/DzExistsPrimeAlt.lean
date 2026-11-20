import Mathlib

/- English proof (translation)
Introduce `F _ _ v n`. Proceed by induction on `n using Nat.recOnMul with`. Consider the case `zero => intro h`. Conclude with `absurd rfl h`. Consider the case `one`.

Introduce `_ h`. Rewrite `h` using `[Nat.cast_one]`. Conclude with `absurd ((Ideal.eq_top_iff_one _).2 h) v.isPrime.ne_top`. Consider the case `prime p hp => intro _ h`. Conclude with `⟨p, hp, dvd_rfl, h⟩`.

Consider the case `mul a b iha ihb`. Introduce `hab h`. Rewrite `h` using `[Nat.cast_mul]`. Break down `v.isPrime.mem_or_mem h with ha | hb` into its components or cases. Take `⟨p, hp, hd, hm⟩` from `iha (left_ne_zero_of_mul hab) ha`.

Conclude with `⟨p, hp, hd.mul_right b, hm⟩`. Take `⟨p, hp, hd, hm⟩` from `ihb (right_ne_zero_of_mul hab) hb`. Conclude with `⟨p, hp, hd.mul_left a, hm⟩`.
-/
theorem UpperTheory.Reformulated.B.Qk5.dz_exists_prime :
    ∀ {F : Type} [inst : Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (n : ℕ),
    n ≠ (0 : ℕ) →
      (↑n : NumberField.RingOfIntegers F) ∈ v.asIdeal →
        ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ (↑p : NumberField.RingOfIntegers F) ∈ v.asIdeal := by
  intro F _ _ v n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    rw [Nat.cast_one] at h
    exact absurd ((Ideal.eq_top_iff_one _).2 h) v.isPrime.ne_top
  | prime p hp => intro _ h; exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b iha ihb =>
    intro hab h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with ha | hb
    · obtain ⟨p, hp, hd, hm⟩ := iha (left_ne_zero_of_mul hab) ha
      exact ⟨p, hp, hd.mul_right b, hm⟩
    · obtain ⟨p, hp, hd, hm⟩ := ihb (right_ne_zero_of_mul hab) hb
      exact ⟨p, hp, hd.mul_left a, hm⟩
