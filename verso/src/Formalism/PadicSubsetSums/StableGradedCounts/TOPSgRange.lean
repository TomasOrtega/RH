import Formalism.PadicSubsetSums.CentralIdempotents.ResidueAvoidanceOfPrimes

namespace Formalism.IrreducibleCountingLemmas.TOP

/- English proof (translation)
Introduce `ℓ s b H hH h1 h2 h3`. Establish `hs0 : (0 : ℝ) < s - 1` using `by linarith`. Establish `hlt : s - 1 < (ℓ : ℝ) - 1` using `by linarith`. Establish `hl0 : (0 : ℝ) < (ℓ : ℝ) - 1` using `by linarith`. Establish `hspos : (0 : ℝ) < s` using `by linarith`.

Establish `step1 : H / ((ℓ : ℝ) - 1) ≤ H / (s - 1)`. Rewrite using `[div_le_div_iff₀ hl0 hs0]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hlt.le hH]`. Establish `step2 : H / (s - 1) ≤ 2 * b / s`. Rewrite using `[div_le_div_iff₀ hs0 hspos]`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `step1.trans step2`.
-/
theorem geomRatioBound : SgRange := by
  intro ℓ s b H hH h1 h2 h3
  have hs0 : (0 : ℝ) < s - 1 := by linarith
  have hlt : s - 1 < (ℓ : ℝ) - 1 := by linarith
  have hl0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hspos : (0 : ℝ) < s := by linarith
  have step1 : H / ((ℓ : ℝ) - 1) ≤ H / (s - 1) := by
    rw [div_le_div_iff₀ hl0 hs0]
    nlinarith [mul_le_mul_of_nonneg_left hlt.le hH]
  have step2 : H / (s - 1) ≤ 2 * b / s := by
    rw [div_le_div_iff₀ hs0 hspos]
    linarith
  exact step1.trans step2

end Formalism.IrreducibleCountingLemmas.TOP
