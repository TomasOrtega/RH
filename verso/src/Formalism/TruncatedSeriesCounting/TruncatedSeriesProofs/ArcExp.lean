import Mathlib
import Formalism.TruncatedSeriesCounting.StatementX

namespace Formalism.TruncatedSeriesCounting.X

/- English proof (authored)
Because G ≥ 0 and j′ ≤ ell, we have j′G ≤ ell·G. If the maximum is 2σ+2j′G+1, bound it by 2σ+2ell·G+1 and add the prefactor. If the maximum is r+κ, the left side becomes 2r+4σ+2κ. The right side is larger by the nonnegative quantity 2σ+2ell·G+1.
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
