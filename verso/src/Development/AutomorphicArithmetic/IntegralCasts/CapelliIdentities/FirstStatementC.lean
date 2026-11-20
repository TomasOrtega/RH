import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. Chain the equalities or inequalities of the calculation.
-/
theorem UpperTheory.Reformulated.B.OneAddPowLeTwoPowMul.main :
    ∀ (t : ℝ), (0 : ℝ) ≤ t → ∀ (N : ℕ), ((1 : ℝ) + t) ^ N ≤ (2 : ℝ) ^ N * ((1 : ℝ) + t ^ N) := by
  intro t ht N
  have h1 : (1 : ℝ) + t ≤ 2 * max 1 t := by
    linarith [le_max_left (1 : ℝ) t, le_max_right (1 : ℝ) t]
  have h2 : ((1 : ℝ) + t) ^ N ≤ (2 * max 1 t) ^ N := pow_le_pow_left₀ (by linarith) h1 N
  rw [mul_pow] at h2
  have h3 : (max (1 : ℝ) t) ^ N ≤ 1 + t ^ N := by
    rcases le_total t 1 with h | h
    · rw [max_eq_left h, one_pow]
      have : (0 : ℝ) ≤ t ^ N := pow_nonneg ht N
      linarith
    · rw [max_eq_right h]
      linarith
  calc ((1 : ℝ) + t) ^ N ≤ 2 ^ N * (max 1 t) ^ N := h2
    _ ≤ 2 ^ N * (1 + t ^ N) := mul_le_mul_of_nonneg_left h3 (by positivity)
