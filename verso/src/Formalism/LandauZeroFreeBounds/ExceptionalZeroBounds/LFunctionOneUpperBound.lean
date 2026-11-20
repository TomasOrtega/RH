import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LDerivNearOne

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Use `⟨38 * Real.exp (3 / 2), ?_⟩` and prove the remaining obligations. Introduce `q _ χ hχ`. Establish `hq : 3 ≤ q` using `three_le_modulus_of_ne_one χ hχ`. Establish `hlog : 2 ≤ Real.log (3 * (q : ℝ))` using `two_le_log_three_mul q hq`. Establish `hd : 0 < 3 / (2 * Real.log (3 * (q : ℝ)))` using `div_pos (by norm_num) (by linarith)`.

Conclude with `lfunction_norm_le_near_one χ hχ 1 (by rw [Complex.one_re]; linarith) (by rw [Complex.one_re]; norm_num) (by rw [norm_one]; norm_num)`.
-/
theorem lfunction_one_upper_bound : LFunctionOneUpperBound := by
  refine ⟨38 * Real.exp (3 / 2), ?_⟩
  intro q _ χ hχ
  have hq : 3 ≤ q := three_le_modulus_of_ne_one χ hχ
  have hlog : 2 ≤ Real.log (3 * (q : ℝ)) := two_le_log_three_mul q hq
  have hd : 0 < 3 / (2 * Real.log (3 * (q : ℝ))) := div_pos (by norm_num) (by linarith)
  exact lfunction_norm_le_near_one χ hχ 1 (by rw [Complex.one_re]; linarith)
    (by rw [Complex.one_re]; norm_num) (by rw [norm_one]; norm_num)

end Formalism.ZeroFreeDirichlet
