import Mathlib

/- English proof (translation)
Introduce `a d h`. Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot => exact bot_le`. Consider the case `coe b`. Establish `h1 : b < ((d+1 : ℕ) : ℕ∞)` using `by exact_mod_cast h`.

Establish `h2 : b ≤ (d : ℕ∞)`. Proceed by induction on `b using ENat.recTopCoe with`. Consider the case `top => exact absurd h1 (not_lt.mpr le_top)`. Consider the case `coe n`. Establish `h3 : n < d + 1` using `by exact_mod_cast h1`.

Conclude with `Nat.lt_succ_iff.mp h3` after adjusting the coercions. Conclude with `h2` after adjusting the coercions.
-/
theorem UpperTheory.Reformulated.B.Yhb2.main :
    ∀ {a : WithBot ℕ∞} {d : ℕ}, a < (↑(d + (1 : ℕ)) : WithBot ℕ∞) → a ≤ (↑d : WithBot ℕ∞) := by
  intro a d h
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    have h1 : b < ((d+1 : ℕ) : ℕ∞) := by exact_mod_cast h
    have h2 : b ≤ (d : ℕ∞) := by
      induction b using ENat.recTopCoe with
      | top => exact absurd h1 (not_lt.mpr le_top)
      | coe n =>
        have h3 : n < d + 1 := by exact_mod_cast h1
        exact_mod_cast Nat.lt_succ_iff.mp h3
    exact_mod_cast h2
