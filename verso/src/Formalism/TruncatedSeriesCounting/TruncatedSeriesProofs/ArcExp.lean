import Mathlib
import Formalism.TruncatedSeriesCounting.StatementX

namespace Formalism.TruncatedSeriesCounting.X

/- English proof (translation)
Introduce `r σ κ G j' ell hr hσ hκ hG hj`. Establish `hj' : (j' : ℝ) ≤ ell` using `by exact_mod_cast hj`. Establish `hjG : (j' : ℝ) * G ≤ ell * G` using `mul_le_mul_of_nonneg_right hj' hG`. Establish `hell : 0 ≤ (ell : ℝ) * G` using `mul_nonneg (Nat.cast_nonneg _) hG`. Break down `le_total (r + κ) (2 * σ + 2 * j' * G + 1) with h | h` into its components or cases.

Rewrite using `[max_eq_right h]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[max_eq_left h]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem arc_exponential_identity : ArcExp := by
  intro r σ κ G j' ell hr hσ hκ hG hj
  have hj' : (j' : ℝ) ≤ ell := by exact_mod_cast hj
  have hjG : (j' : ℝ) * G ≤ ell * G := mul_le_mul_of_nonneg_right hj' hG
  have hell : 0 ≤ (ell : ℝ) * G := mul_nonneg (Nat.cast_nonneg _) hG
  rcases le_total (r + κ) (2 * σ + 2 * j' * G + 1) with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

end Formalism.TruncatedSeriesCounting.X
