import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset

/- English proof (translation)
Introduce `d u τ`. Establish `hN : (d.N : ℝ) ≠ 0`. Use `d.two_le_N` as an intermediate fact. Conclude with `(by omega : d.N ≠ 0)` after adjusting the coercions. Establish `hNpos : (0 : ℝ) ≤ d.N` using `Nat.cast_nonneg _`.

Establish `key : (d.N : ℝ) * |ubar d u τ| = |∑ i : Fin d.N, u (τ, i)|`. Unfold `ubar`. Rewrite using `[abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (d.N : ℝ)), ← mul_assoc, mul_one_div_cancel hN, one_mul]`. Rewrite using `[key]`. Conclude with `abs_sum_le_sum_abs _ _`.
-/
theorem NormUbar.proof : NormUbar.Statement := by
  intro d u τ
  have hN : (d.N : ℝ) ≠ 0 := by
    have := d.two_le_N
    exact_mod_cast (by omega : d.N ≠ 0)
  have hNpos : (0 : ℝ) ≤ d.N := Nat.cast_nonneg _
  have key : (d.N : ℝ) * |ubar d u τ| = |∑ i : Fin d.N, u (τ, i)| := by
    unfold ubar
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (d.N : ℝ)), ← mul_assoc,
      mul_one_div_cancel hN, one_mul]
  rw [key]
  exact abs_sum_le_sum_abs _ _

end GroundTheory.Heights₂.Heights.TheoremB
