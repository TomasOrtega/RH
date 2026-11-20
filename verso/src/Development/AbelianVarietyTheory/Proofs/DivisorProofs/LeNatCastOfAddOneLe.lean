import Mathlib

namespace GlobalTheory.NatCastUpperBound

/- English proof (translation)
Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot => exact bot_le`. Consider the case `coe b`. Proceed by induction on `b using ENat.recTopCoe with`. Consider the case `top`.

It suffices to derive a contradiction. Establish `h1 : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞)` using `rfl`. Establish `h2 : ((n + 1 : ℕ) : WithBot ℕ∞) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)` using `rfl`. Rewrite `h` using `[h1, h2, WithBot.coe_le_coe, top_le_iff]`. Conclude with `ENat.coe_ne_top _ h`.

Consider the case `coe m`. Establish `h1 : ((m : ℕ∞) : WithBot ℕ∞) + 1 = (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)` using `rfl`. Establish `h2 : ((n + 1 : ℕ) : WithBot ℕ∞) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)` using `rfl`. Establish `h3 : ((n : ℕ) : WithBot ℕ∞) = (((n : ℕ) : ℕ∞) : WithBot ℕ∞)` using `rfl`. Rewrite `h` using `[h1, h2, WithBot.coe_le_coe, ENat.coe_le_coe]`.

Rewrite using `[h3, WithBot.coe_le_coe, ENat.coe_le_coe]`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_natCast_of_add_one_le {a : WithBot ℕ∞} {n : ℕ}
    (h : a + (1 : WithBot ℕ∞) ≤ (↑(n + (1 : ℕ)) : WithBot ℕ∞)) :
    a ≤ (↑n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := rfl
      have h2 : ((n + 1 : ℕ) : WithBot ℕ∞) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      rw [h1, h2, WithBot.coe_le_coe, top_le_iff] at h
      exact ENat.coe_ne_top _ h
    | coe m =>
      have h1 : ((m : ℕ∞) : WithBot ℕ∞) + 1 = (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      have h2 : ((n + 1 : ℕ) : WithBot ℕ∞) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      have h3 : ((n : ℕ) : WithBot ℕ∞) = (((n : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      rw [h1, h2, WithBot.coe_le_coe, ENat.coe_le_coe] at h
      rw [h3, WithBot.coe_le_coe, ENat.coe_le_coe]
      omega

end GlobalTheory.NatCastUpperBound
