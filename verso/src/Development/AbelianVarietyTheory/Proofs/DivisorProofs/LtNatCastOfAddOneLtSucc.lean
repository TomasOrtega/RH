import Mathlib

namespace GlobalTheory.NatCastStrictBound

/- English proof (translation)
Introduce `a n h`. Assume the negation of the conclusion as `hc`. Establish `hle : (↑n : WithBot ℕ∞) ≤ a` using `not_lt.mp hc`. Establish `h2 : (↑n : WithBot ℕ∞) + 1 ≤ a + 1` using `by gcongr`. Rewrite `h` using `[Nat.cast_add, Nat.cast_one]`.

Conclude with `absurd h (not_lt.mpr h2)`.
-/
theorem lt_natCast_of_add_one_lt_succ :
    ∀ {a : WithBot ℕ∞} {n : ℕ}, a + (1 : WithBot ℕ∞) < (↑(n + (1 : ℕ)) : WithBot ℕ∞) →
      a < (↑n : WithBot ℕ∞) := by
  intro a n h
  by_contra hc
  have hle : (↑n : WithBot ℕ∞) ≤ a := not_lt.mp hc
  have h2 : (↑n : WithBot ℕ∞) + 1 ≤ a + 1 := by gcongr
  rw [Nat.cast_add, Nat.cast_one] at h
  exact absurd h (not_lt.mpr h2)

end GlobalTheory.NatCastStrictBound
