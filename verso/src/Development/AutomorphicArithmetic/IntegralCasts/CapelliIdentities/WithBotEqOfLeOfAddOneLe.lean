import Mathlib

/- English proof (translation)
Introduce `x c h1 h2`. Proceed by induction on `x using WithBot.recBotCoe with`. Consider the case `bot => exact le_antisymm bot_le h1`. Consider the case `coe y`. Proceed by induction on `y using ENat.recTopCoe with`.

Consider the case `top`. It suffices to derive a contradiction. Establish `h3 : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((c + 1 : ℕ) : ℕ∞)` using `by exact_mod_cast h2`. Rewrite `h3` using `[top_add, top_le_iff]`. Conclude with `ENat.coe_ne_top _ h3`.

Consider the case `coe n`. Establish `h3 : c ≤ n` using `by exact_mod_cast h1`. Establish `h4 : n + 1 ≤ c + 1` using `by exact_mod_cast h2`. Establish `h5 : n = c` using `by omega`. Substitute `h5` using the available equality.

Both sides reduce to the same expression.
-/
theorem UpperTheory.Reformulated.B.Ydd3.withBot_eq_of_le_of_add_one_le :
    ∀ {x : WithBot ℕ∞} {c : ℕ},
      (↑c : WithBot ℕ∞) ≤ x → x + (1 : WithBot ℕ∞) ≤ (↑(c + (1 : ℕ)) : WithBot ℕ∞) → x = (↑c : WithBot ℕ∞) := by
  intro x c h1 h2
  induction x using WithBot.recBotCoe with
  | bot => exact le_antisymm bot_le h1
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h3 : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((c + 1 : ℕ) : ℕ∞) := by exact_mod_cast h2
      rw [top_add, top_le_iff] at h3
      exact ENat.coe_ne_top _ h3
    | coe n =>
      have h3 : c ≤ n := by exact_mod_cast h1
      have h4 : n + 1 ≤ c + 1 := by exact_mod_cast h2
      have h5 : n = c := by omega
      subst h5
      rfl
