import Mathlib

namespace ReciprocityTheory.GeometryOfNumbersTheory

/- English proof (translation)
Establish `hN : (0 : ℝ) < Fintype.card ι` using `Nat.cast_pos.mpr Fintype.card_pos`. Use `set M := 1 + (∑ σ, t σ) / Fintype.card ι with hM`. Establish `hM0 : 0 < M`. Establish `: 0 ≤ (∑ σ, t σ) / Fintype.card ι` using `div_nonneg (Finset.sum_nonneg fun σ _ => ht σ) hN.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hpt : ∀ σ, Real.log (1 + t σ) ≤ Real.log M + ((1 + t σ) / M - 1)` using `fun σ => by`. Establish `hy : 0 < 1 + t σ` using `by linarith [ht σ]`. Use `Real.log_le_sub_one_of_pos (div_pos hy hM0)` as an intermediate fact. Rewrite `this` using `[Real.log_div hy.ne' hM0.ne']`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `(Finset.sum_le_sum fun σ _ => hpt σ).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Establish `: (Fintype.card ι : ℝ) * 1 + ∑ σ, t σ = Fintype.card ι * M`. Rewrite using `[hM]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this, mul_div_cancel_right₀ _ hM0.ne']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wma_sum_log_le {ι : Type} [Fintype ι] [Nonempty ι] (t : ι → ℝ) (ht : ∀ σ, 0 ≤ t σ) :
    ∑ σ, Real.log (1 + t σ) ≤
      Fintype.card ι * Real.log (1 + (∑ σ, t σ) / Fintype.card ι) := by
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  set M := 1 + (∑ σ, t σ) / Fintype.card ι with hM
  have hM0 : 0 < M := by
    have : 0 ≤ (∑ σ, t σ) / Fintype.card ι := div_nonneg (Finset.sum_nonneg fun σ _ => ht σ) hN.le
    linarith
  have hpt : ∀ σ, Real.log (1 + t σ) ≤ Real.log M + ((1 + t σ) / M - 1) := fun σ => by
    have hy : 0 < 1 + t σ := by linarith [ht σ]
    have := Real.log_le_sub_one_of_pos (div_pos hy hM0)
    rw [Real.log_div hy.ne' hM0.ne'] at this
    linarith
  refine (Finset.sum_le_sum fun σ _ => hpt σ).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_sub_distrib,
    ← Finset.sum_div, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card ι : ℝ) * 1 + ∑ σ, t σ = Fintype.card ι * M := by
    rw [hM]; field_simp
  rw [this, mul_div_cancel_right₀ _ hM0.ne']
  ring

end ReciprocityTheory.GeometryOfNumbersTheory
