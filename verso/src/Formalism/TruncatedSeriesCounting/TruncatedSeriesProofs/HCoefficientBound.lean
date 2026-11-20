import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

/- English proof (translation)
Establish `hy : 0 ≤ x - 11` using `by linarith`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg hy hy) hy, mul_nonneg hy hy]`.
-/
private lemma hCoef_num (x : ℝ) (hx : 11 ≤ x) : 0 ≤ 7 * x ^ 3 - 78 * x ^ 2 + 95 * x - 32 := by

  have hy : 0 ≤ x - 11 := by linarith
  nlinarith [mul_nonneg (mul_nonneg hy hy) hy, mul_nonneg hy hy]

/- English proof (translation)
Introduce `x hx`. Establish `h0 : (0 : ℝ) < x` using `by linarith`. Establish `h1 : (0 : ℝ) < x - 1` using `by linarith`. Establish `hx0 : x ≠ 0` using `ne_of_gt h0`. Establish `hx1 : x - 1 ≠ 0` using `ne_of_gt h1`.

Establish `key` using `hCoef_num x hx`. Establish `e : 32 / x ^ 2 - (8 * (2 * x - 1) / (x - 1) ^ 3 + 8 / (x - 1) ^ 2 + 1 / (x * (x - 1))) = (7 * x ^ 3 - 78 * x ^ 2 + 95 * x - 32) / (x ^ 2 * (x - 1) ^ 3)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hd : 0 ≤ (7 * x ^ 3 - 78 * x ^ 2 + 95 * x - 32) / (x ^ 2 * (x - 1) ^ 3)` using `div_nonneg key (by positivity)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem h_coefficient_bound : HCoef := by
  intro x hx
  have h0 : (0 : ℝ) < x := by linarith
  have h1 : (0 : ℝ) < x - 1 := by linarith
  have hx0 : x ≠ 0 := ne_of_gt h0
  have hx1 : x - 1 ≠ 0 := ne_of_gt h1
  have key := hCoef_num x hx
  have e : 32 / x ^ 2 - (8 * (2 * x - 1) / (x - 1) ^ 3 + 8 / (x - 1) ^ 2 + 1 / (x * (x - 1)))
      = (7 * x ^ 3 - 78 * x ^ 2 + 95 * x - 32) / (x ^ 2 * (x - 1) ^ 3) := by
    field_simp
    ring
  have hd : 0 ≤ (7 * x ^ 3 - 78 * x ^ 2 + 95 * x - 32) / (x ^ 2 * (x - 1) ^ 3) :=
    div_nonneg key (by positivity)
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
