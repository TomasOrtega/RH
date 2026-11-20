import Mathlib

/- English proof (translation)
Introduce `a k h`. Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot => exact bot_le`. Consider the case `coe a`. Proceed by induction on `a using ENat.recTopCoe with`.

Consider the case `top`. It suffices to derive a contradiction. Establish `h1 : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞)`. Rewrite using `[← WithBot.coe_le_coe]`. Conclude with `h`.

Rewrite `h1` using `[top_add, top_le_iff]`. Conclude with `ENat.coe_ne_top _ h1`. Consider the case `coe n`. Establish `h1 : ((n : ℕ∞) + 1 : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞)`. Rewrite using `[← WithBot.coe_le_coe]`.

Conclude with `h`. Establish `h2 : n + 1 ≤ k + 1` using `by exact_mod_cast h1`. Establish `h3 : (n : ℕ∞) ≤ (k : ℕ∞)` using `by exact_mod_cast (Nat.le_of_succ_le_succ h2)`. Conclude with `WithBot.coe_le_coe.mpr h3`.
-/
theorem UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ :
    ∀ {a : WithBot ℕ∞} {k : ℕ},
    a + (1 : WithBot ℕ∞) ≤ (↑(k + (1 : ℕ)) : WithBot ℕ∞) → a ≤ (↑k : WithBot ℕ∞) := by
  intro a k h
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := by
        rw [← WithBot.coe_le_coe]
        exact h
      rw [top_add, top_le_iff] at h1
      exact ENat.coe_ne_top _ h1
    | coe n =>
      have h1 : ((n : ℕ∞) + 1 : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := by
        rw [← WithBot.coe_le_coe]
        exact h
      have h2 : n + 1 ≤ k + 1 := by exact_mod_cast h1
      have h3 : (n : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast (Nat.le_of_succ_le_succ h2)
      exact WithBot.coe_le_coe.mpr h3
