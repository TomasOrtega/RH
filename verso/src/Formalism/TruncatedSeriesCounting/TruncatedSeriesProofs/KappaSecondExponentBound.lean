import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

/- English proof (translation)
Introduce `ℓ hℓ b b' S h'' E s₂ L c' hE hs hL hc`. Establish `hℓ' : (2 : ℝ) ≤ (ℓ : ℝ)` using `by exact_mod_cast hℓ`. Establish `hl1 : (0 : ℝ) < (ℓ : ℝ) - 1` using `by linarith`. Establish `hl0 : (0 : ℝ) < (ℓ : ℝ)` using `by linarith`. Establish `hb : (0 : ℝ) ≤ (b : ℝ)` using `Nat.cast_nonneg b`.

Establish `hS : (0 : ℝ) ≤ (S : ℝ)` using `Nat.cast_nonneg S`. Establish `hcast : (((b + S + 1 : ℕ) : ℝ)) = (b : ℝ) + (S : ℝ) + 1` using `by push_cast; ring`. Establish `e2 : (b : ℝ) / ((ℓ : ℝ) - 1) = (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) + (b : ℝ) / (ℓ : ℝ)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `e1 : ((b : ℝ) + (S : ℝ) + 1) / ((ℓ : ℝ) - 1) = (b : ℝ) / ((ℓ : ℝ) - 1) + ((S : ℝ) + 1) / ((ℓ : ℝ) - 1)` using `by ring`. Establish `e3 : ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) ≤ (S : ℝ) + 1`. Establish `hq : 0 ≤ ((S : ℝ) + 1) / ((ℓ : ℝ) - 1)` using `div_nonneg (by linarith) hl1.le`. Establish `hm : ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) * ((ℓ : ℝ) - 1) = (S : ℝ) + 1`. Clear the denominators using the available nonvanishing facts.

Use polynomial arithmetic with `[mul_nonneg hq (by linarith : (0 : ℝ) ≤ (ℓ : ℝ) - 2)]`. Establish `h4 : 0 ≤ (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1))` using `div_nonneg hb (mul_pos hl0 hl1).le`. Rewrite using `[hcast]`. Apply `max_le` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[e1, e2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem second_exponent_bound : MaxZeroExponentInequality := by
  intro ℓ hℓ b b' S h'' E s₂ L c' hE hs hL hc
  have hℓ' : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hl1 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hl0 : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hS : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
  have hcast : (((b + S + 1 : ℕ) : ℝ)) = (b : ℝ) + (S : ℝ) + 1 := by push_cast; ring

  have e2 : (b : ℝ) / ((ℓ : ℝ) - 1) = (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) + (b : ℝ) / (ℓ : ℝ) := by
    field_simp
    ring
  have e1 : ((b : ℝ) + (S : ℝ) + 1) / ((ℓ : ℝ) - 1)
      = (b : ℝ) / ((ℓ : ℝ) - 1) + ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) := by ring

  have e3 : ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) ≤ (S : ℝ) + 1 := by
    have hq : 0 ≤ ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) := div_nonneg (by linarith) hl1.le
    have hm : ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) * ((ℓ : ℝ) - 1) = (S : ℝ) + 1 := by
      field_simp
    nlinarith [mul_nonneg hq (by linarith : (0 : ℝ) ≤ (ℓ : ℝ) - 2)]
  have h4 : 0 ≤ (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) := div_nonneg hb (mul_pos hl0 hl1).le
  rw [hcast]
  apply max_le
  · linarith
  · rw [e1, e2]
    linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
