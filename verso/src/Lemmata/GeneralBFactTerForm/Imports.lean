import Mathlib

namespace Bl.general_b_fact_ter_form

/- English proof (translation)
Introduce `x m h`. Proceed by induction on `x using WithBot.recBotCoe with`. Consider the case `bot`. It suffices to derive a contradiction. Establish `e : ((m + 1 : ℕ) : WithBot ENat) = (((m : ENat) + 1 : ENat) : WithBot ENat)`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hb : (⊥ : WithBot ENat) + 1 = ⊥` using `WithBot.bot_add _`. Rewrite `h` using `[e, hb]`. Conclude with `WithBot.bot_ne_coe h`.

Consider the case `coe y`. Establish `h2 : ((y + 1 : ENat) : WithBot ENat) = (((m : ENat) + 1 : ENat) : WithBot ENat)`. Rewrite using `[WithBot.coe_add, WithBot.coe_one]`. Rewrite using `[h]`. Use `push_cast`.

Both sides reduce to the same expression. Establish `h3 : y + 1 = (m : ENat) + 1` using `WithBot.coe_injective h2`. Establish `h4 : y = (m : ENat)`. Use `(ENat.add_left_injective_of_ne_top (n := 1) ENat.one_ne_top) h3` as an intermediate fact. Conclude with `this`.

Rewrite using `[h4]`. Both sides reduce to the same expression.
-/
theorem goal1 :
  ∀ {x : WithBot.{0} ENat} {m : Nat},
  Eq.{1} (HAdd.hAdd.{0, 0, 0} x 1) (Nat.cast.{0} (HAdd.hAdd.{0, 0, 0} m 1)) → Eq.{1} x (Nat.cast.{0} m) := by
  intro x m h
  induction x using WithBot.recBotCoe with
  | bot =>
    exfalso
    have e : ((m + 1 : ℕ) : WithBot ENat) = (((m : ENat) + 1 : ENat) : WithBot ENat) := by
      push_cast
      rfl
    have hb : (⊥ : WithBot ENat) + 1 = ⊥ := WithBot.bot_add _
    rw [e, hb] at h
    exact WithBot.bot_ne_coe h
  | coe y =>
    have h2 : ((y + 1 : ENat) : WithBot ENat) = (((m : ENat) + 1 : ENat) : WithBot ENat) := by
      rw [WithBot.coe_add, WithBot.coe_one]
      rw [h]
      push_cast
      rfl
    have h3 : y + 1 = (m : ENat) + 1 := WithBot.coe_injective h2
    have h4 : y = (m : ENat) := by
      have := (ENat.add_left_injective_of_ne_top (n := 1) ENat.one_ne_top) h3
      exact this
    rw [h4]
    rfl

end Bl.general_b_fact_ter_form
