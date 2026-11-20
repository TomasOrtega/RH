import Mathlib

namespace Bl.general_b_fact_bis

/- English proof (translation)
Introduce `x m h`. Proceed by induction on `x using WithBot.recBotCoe with`. Consider the case `bot`. Rewrite `h` using `[WithBot.bot_add, ← WithBot.coe_natCast]`. Conclude with `absurd h.symm WithBot.coe_ne_bot`.

Consider the case `coe e`. Rewrite `h` using `[← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_natCast, WithBot.coe_inj]`. Rewrite using `[← WithBot.coe_natCast, WithBot.coe_inj]`. Proceed by induction on `e using ENat.recTopCoe with`. Consider the case `top`.

Rewrite `h` using `[top_add]`. Conclude with `absurd h.symm (ENat.natCast_ne_top _)`. Consider the case `coe n`. Rewrite `h` using `[← ENat.natCast_one, ← ENat.natCast_add, ENat.natCast_inj]`. Rewrite using `[ENat.natCast_inj]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem goal1 :
  ∀ {x : WithBot.{0} ENat} {m : Nat},
  Eq.{1} (HAdd.hAdd.{0, 0, 0} x 1) (Nat.cast.{0} (HAdd.hAdd.{0, 0, 0} m 1)) → Eq.{1} x (Nat.cast.{0} m) := by
  intro x m h
  induction x using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add, ← WithBot.coe_natCast] at h
    exact absurd h.symm WithBot.coe_ne_bot
  | coe e =>
    rw [← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_natCast, WithBot.coe_inj] at h
    rw [← WithBot.coe_natCast, WithBot.coe_inj]
    induction e using ENat.recTopCoe with
    | top =>
      rw [top_add] at h
      exact absurd h.symm (ENat.natCast_ne_top _)
    | coe n =>
      rw [← ENat.natCast_one, ← ENat.natCast_add, ENat.natCast_inj] at h
      rw [ENat.natCast_inj]
      omega

end Bl.general_b_fact_bis
