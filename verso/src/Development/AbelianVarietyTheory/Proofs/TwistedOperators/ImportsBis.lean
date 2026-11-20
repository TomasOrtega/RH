import Mathlib

namespace GlobalTheory.OneAddPowBoundTwistedOperators

/- English proof (translation)
Introduce `L hL N`. Establish `h2 : (0 : ℝ) ≤ (2 : ℝ) ^ N` using `by positivity`. Establish `hLN : (0 : ℝ) ≤ L ^ N` using `pow_nonneg hL N`. Break down `le_total L 1 with h | h` into its components or cases. Establish `h1 : ((1 : ℝ) + L) ^ N ≤ (2 : ℝ) ^ N` using `pow_le_pow_left₀ (by linarith) (by linarith) N`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h1 : ((1 : ℝ) + L) ^ N ≤ (2 * L) ^ N` using `pow_le_pow_left₀ (by linarith) (by linarith) N`. Rewrite `h1` using `[mul_pow]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_add_pow_le : ∀ {L : ℝ}, (0 : ℝ) ≤ L → ∀ (N : ℕ), ((1 : ℝ) + L) ^ N ≤ (2 : ℝ) ^ N * ((1 : ℝ) + L ^ N) := by
  intro L hL N
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ N := by positivity
  have hLN : (0 : ℝ) ≤ L ^ N := pow_nonneg hL N
  rcases le_total L 1 with h | h
  · have h1 : ((1 : ℝ) + L) ^ N ≤ (2 : ℝ) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    nlinarith
  · have h1 : ((1 : ℝ) + L) ^ N ≤ (2 * L) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    rw [mul_pow] at h1
    nlinarith

end GlobalTheory.OneAddPowBoundTwistedOperators
