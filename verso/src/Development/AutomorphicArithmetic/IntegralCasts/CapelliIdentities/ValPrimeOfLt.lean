import Mathlib

/- English proof (translation)
Introduce `Ω _ A n`. Proceed by induction on `n using induction_on_primes with`. Consider the case `zero => intro h`. Conclude with `absurd rfl h`. Consider the case `one => intro _ h`.

Simplify using `at h`. Consider the case `prime_mul p a hp ih`. Introduce `hne h`. Establish `ha : a ≠ 0` using `right_ne_zero_of_mul hne`. Distinguish the cases in `hpv : A.valuation (p : Ω) < 1`.

Conclude with `⟨p, hp, dvd_mul_right p a, hpv⟩`. Establish `hav : A.valuation (a : Ω) < 1`. Assume the negation of the conclusion as `hc`. Rewrite `h` using `[Nat.cast_mul, map_mul]`. Conclude with `absurd h (not_lt.mpr (one_le_mul (not_lt.mp hpv) (not_lt.mp hc)))`.

Take `⟨t, ht, hd, hv⟩` from `ih ha hav`. Conclude with `⟨t, ht, hd.mul_left p, hv⟩`.
-/
theorem UpperTheory.Reformulated.B.Qi55.val_prime_of_lt :
    ∀ {Ω : Type} [inst : Field Ω]
    (A : ValuationSubring Ω) (n : ℕ),
    n ≠ (0 : ℕ) →
      (A.valuation : Ω → A.ValueGroup) (↑n : Ω) < (1 : A.ValueGroup) →
        ∃ (t : ℕ), Nat.Prime t ∧ t ∣ n ∧ (A.valuation : Ω → A.ValueGroup) (↑t : Ω) < (1 : A.ValueGroup) := by
  intro Ω _ A n
  induction n using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one => intro _ h; simp at h
  | prime_mul p a hp ih =>
    intro hne h
    have ha : a ≠ 0 := right_ne_zero_of_mul hne
    by_cases hpv : A.valuation (p : Ω) < 1
    · exact ⟨p, hp, dvd_mul_right p a, hpv⟩
    · have hav : A.valuation (a : Ω) < 1 := by
        by_contra hc
        rw [Nat.cast_mul, map_mul] at h
        exact absurd h (not_lt.mpr (one_le_mul (not_lt.mp hpv) (not_lt.mp hc)))
      obtain ⟨t, ht, hd, hv⟩ := ih ha hav
      exact ⟨t, ht, hd.mul_left p, hv⟩
