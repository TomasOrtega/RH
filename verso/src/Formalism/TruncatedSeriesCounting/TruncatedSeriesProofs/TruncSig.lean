import Mathlib
import Formalism.TruncatedSeriesCounting.StatementX

namespace Formalism.TruncatedSeriesCounting.X

/- English proof (translation)
Unfold `TruncSig`. Introduce `ℓ hℓ y X M η`. Establish `hl : (3 : ℝ) ≤ (ℓ : ℝ)` using `by exact_mod_cast hℓ`. Establish `ha : (0 : ℝ) < (ℓ : ℝ) - 1` using `by linarith`. Establish `hlpos : (0 : ℝ) < (ℓ : ℝ)` using `by linarith`.

Establish `hy : (0 : ℝ) ≤ (y : ℝ)` using `Nat.cast_nonneg y`. Establish `gen : ∀ T : ℝ, 0 ≤ T → (y : ℝ) * ℓ / (ℓ - 1) - max 0 ((ℓ : ℝ) * y - T) ≤ T / (ℓ - 1)`. Introduce `T hT`. Rewrite using `[sub_le_iff_le_add, div_le_iff₀ ha, add_mul, div_mul_cancel₀ _ (ne_of_gt ha)]`. Break down `le_total ((ℓ : ℝ) * y - T) 0 with h | h` into its components or cases.

Rewrite using `[max_eq_left h]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[max_eq_right h]`. Use polynomial arithmetic with `[mul_nonneg h (by linarith : (0 : ℝ) ≤ (ℓ : ℝ) - 2)]`. Establish `mono : ∀ T : ℝ, T / ((ℓ : ℝ) - 1) ≤ (T + 1) / ((ℓ : ℝ) - 1) + 1`.

Introduce `T`. Establish `h1 : 0 ≤ 1 / ((ℓ : ℝ) - 1)` using `by positivity`. Rewrite using `[add_div]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(gen X (Nat.cast_nonneg _)).trans (mono _)`. Establish `e : (ℓ : ℝ) * y - η - M = (ℓ : ℝ) * y - (η + M)` using `by ring`. Rewrite using `[e]`. Use `gen ((η : ℝ) + M) (by positivity)` as an intermediate fact. Establish `h2 : ((η : ℝ) + M) / (ℓ - 1) ≤ ((M : ℝ) + η) / (ℓ - 1) + 1`.

Rewrite using `[add_comm (η : ℝ)]`. Establish `h3 : 0 ≤ 1 / ((ℓ : ℝ) - 1)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsq : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2` using `pow_pos ha 2`.

Establish `e : (y : ℝ) * ℓ / (ℓ - 1) = (y : ℝ) * ℓ * (ℓ - 1) / (ℓ - 1) ^ 2`. Clear the denominators using the available nonvanishing facts. Establish `key : (y : ℝ) * ℓ / (ℓ - 1) - max 0 (((ℓ : ℝ) - 1) * y - X / ℓ) ≤ X / (ℓ - 1) ^ 2`. Rewrite using `[e, sub_le_iff_le_add, div_le_iff₀ hsq, add_mul, div_mul_cancel₀ _ (ne_of_gt hsq)]`. Establish `hX : (X : ℝ) = X / ℓ * ℓ` using `(div_mul_cancel₀ _ hlpos.ne').symm`.

Break down `le_total (((ℓ : ℝ) - 1) * y - X / ℓ) 0 with h | h` into its components or cases. Rewrite using `[max_eq_left h]`. Establish `h4 : ((ℓ : ℝ) - 1) * y * ℓ ≤ X`. Establish `h5 : ((ℓ : ℝ) - 1) * y ≤ X / ℓ` using `by linarith`. Use `mul_le_mul_of_nonneg_right h5 hlpos.le` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[max_eq_right h]`. Establish `hs2 : (0 : ℝ) ≤ ((ℓ : ℝ) - 1) ^ 2 - ℓ` using `by nlinarith`. Use polynomial arithmetic with `[mul_nonneg h hs2]`.

Establish `h6 : (0 : ℝ) ≤ 1` using `zero_le_one`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem truncation_signature_bound : TruncSig := by
  unfold TruncSig
  intro ℓ hℓ y X M η
  have hl : (3 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have ha : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hlpos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hy : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  have gen : ∀ T : ℝ, 0 ≤ T → (y : ℝ) * ℓ / (ℓ - 1) - max 0 ((ℓ : ℝ) * y - T) ≤ T / (ℓ - 1) := by
    intro T hT
    rw [sub_le_iff_le_add, div_le_iff₀ ha, add_mul, div_mul_cancel₀ _ (ne_of_gt ha)]
    rcases le_total ((ℓ : ℝ) * y - T) 0 with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]
      nlinarith [mul_nonneg h (by linarith : (0 : ℝ) ≤ (ℓ : ℝ) - 2)]
  have mono : ∀ T : ℝ, T / ((ℓ : ℝ) - 1) ≤ (T + 1) / ((ℓ : ℝ) - 1) + 1 := by
    intro T
    have h1 : 0 ≤ 1 / ((ℓ : ℝ) - 1) := by positivity
    rw [add_div]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · exact (gen X (Nat.cast_nonneg _)).trans (mono _)
  · have e : (ℓ : ℝ) * y - η - M = (ℓ : ℝ) * y - (η + M) := by ring
    rw [e]
    have := gen ((η : ℝ) + M) (by positivity)
    have h2 : ((η : ℝ) + M) / (ℓ - 1) ≤ ((M : ℝ) + η) / (ℓ - 1) + 1 := by
      rw [add_comm (η : ℝ)]
      have h3 : 0 ≤ 1 / ((ℓ : ℝ) - 1) := by positivity
      linarith
    linarith
  · have hsq : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2 := pow_pos ha 2
    have e : (y : ℝ) * ℓ / (ℓ - 1) = (y : ℝ) * ℓ * (ℓ - 1) / (ℓ - 1) ^ 2 := by
      field_simp
    have key : (y : ℝ) * ℓ / (ℓ - 1) - max 0 (((ℓ : ℝ) - 1) * y - X / ℓ) ≤ X / (ℓ - 1) ^ 2 := by
      rw [e, sub_le_iff_le_add, div_le_iff₀ hsq, add_mul, div_mul_cancel₀ _ (ne_of_gt hsq)]
      have hX : (X : ℝ) = X / ℓ * ℓ := (div_mul_cancel₀ _ hlpos.ne').symm
      rcases le_total (((ℓ : ℝ) - 1) * y - X / ℓ) 0 with h | h
      · rw [max_eq_left h]
        have h4 : ((ℓ : ℝ) - 1) * y * ℓ ≤ X := by
          have h5 : ((ℓ : ℝ) - 1) * y ≤ X / ℓ := by linarith
          have := mul_le_mul_of_nonneg_right h5 hlpos.le
          linarith
        nlinarith
      · rw [max_eq_right h]
        have hs2 : (0 : ℝ) ≤ ((ℓ : ℝ) - 1) ^ 2 - ℓ := by nlinarith
        nlinarith [mul_nonneg h hs2]
    have h6 : (0 : ℝ) ≤ 1 := zero_le_one
    linarith

end Formalism.TruncatedSeriesCounting.X
