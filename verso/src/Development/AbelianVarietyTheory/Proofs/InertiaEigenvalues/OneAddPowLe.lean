import Mathlib

namespace GlobalTheory.OneAddPowBound

/- English proof (translation)
Introduce `t ht k`. Establish `htk : 0 ≤ t ^ k` using `pow_nonneg ht k`. Establish `h2 : (0 : ℝ) ≤ 2 ^ k` using `pow_nonneg (by norm_num) k`. Establish `h1 : (0 : ℝ) ≤ 1 + t` using `by linarith`. Break down `le_total t 1 with h | h` into its components or cases.

Establish `ha : (1 + t) ^ k ≤ (2 : ℝ) ^ k` using `pow_le_pow_left₀ h1 (by linarith) k`. Establish `hb : (2 : ℝ) ^ k * 1 ≤ 2 ^ k * (1 + t ^ k)` using `mul_le_mul_of_nonneg_left (by linarith) h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha : (1 + t) ^ k ≤ (2 * t) ^ k` using `pow_le_pow_left₀ h1 (by linarith) k`. Rewrite `ha` using `[mul_pow]`.

Establish `hb : (2 : ℝ) ^ k * t ^ k ≤ 2 ^ k * (1 + t ^ k)` using `mul_le_mul_of_nonneg_left (by linarith) h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_add_pow_le : ∀ {t : ℝ}, (0 : ℝ) ≤ t → ∀ (k : ℕ),
    ((1 : ℝ) + t) ^ k ≤ (2 : ℝ) ^ k * ((1 : ℝ) + t ^ k) := by
  intro t ht k
  have htk : 0 ≤ t ^ k := pow_nonneg ht k
  have h2 : (0 : ℝ) ≤ 2 ^ k := pow_nonneg (by norm_num) k
  have h1 : (0 : ℝ) ≤ 1 + t := by linarith
  rcases le_total t 1 with h | h
  · have ha : (1 + t) ^ k ≤ (2 : ℝ) ^ k := pow_le_pow_left₀ h1 (by linarith) k
    have hb : (2 : ℝ) ^ k * 1 ≤ 2 ^ k * (1 + t ^ k) :=
      mul_le_mul_of_nonneg_left (by linarith) h2
    linarith
  · have ha : (1 + t) ^ k ≤ (2 * t) ^ k := pow_le_pow_left₀ h1 (by linarith) k
    rw [mul_pow] at ha
    have hb : (2 : ℝ) ^ k * t ^ k ≤ 2 ^ k * (1 + t ^ k) :=
      mul_le_mul_of_nonneg_left (by linarith) h2
    linarith

end GlobalTheory.OneAddPowBound
