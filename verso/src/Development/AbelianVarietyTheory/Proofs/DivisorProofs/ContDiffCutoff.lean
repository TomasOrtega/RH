import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
open Filter Topology Set Metric MeasureTheory GlobalTheory.ChernReg
open scoped ContDiff

namespace GlobalTheory.ChernReg

open Polynomial in

/- English proof (translation)
Establish `h : ContDiff ℝ ∞ (fun t : ℝ => (X ^ 2 : ℝ[X]).eval (1 - t)⁻¹ * expNegInvGlue (1 - t))` using `(expNegInvGlue.contDiff_polynomial_eval_inv_mul (n := ⊤) (X ^ 2)).comp (contDiff_const.sub contDiff_id)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `t`. Unfold `cutoff expNegInvGlue`. Distinguish the cases in `ht : t < 1`.

Establish `h1 : ¬ (1 - t ≤ 0)` using `by linarith`. Rewrite using `[if_pos ht, if_neg h1, eval_pow, eval_X, inv_pow]`. Use `congr 2`. Rewrite using `[← neg_sub 1 t, inv_neg]`. Establish `h1 : 1 - t ≤ 0` using `by linarith`.

Rewrite using `[if_neg ht, if_pos h1, mul_zero]`.
-/
theorem contDiff_cutoff : ContDiff ℝ ∞ GlobalTheory.ChernReg.cutoff := by
  have h : ContDiff ℝ ∞ (fun t : ℝ => (X ^ 2 : ℝ[X]).eval (1 - t)⁻¹ * expNegInvGlue (1 - t)) :=
    (expNegInvGlue.contDiff_polynomial_eval_inv_mul (n := ⊤) (X ^ 2)).comp
      (contDiff_const.sub contDiff_id)
  convert h using 1
  funext t
  unfold cutoff expNegInvGlue
  by_cases ht : t < 1
  · have h1 : ¬ (1 - t ≤ 0) := by linarith
    rw [if_pos ht, if_neg h1, eval_pow, eval_X, inv_pow]
    congr 2
    rw [← neg_sub 1 t, inv_neg]
  · have h1 : 1 - t ≤ 0 := by linarith
    rw [if_neg ht, if_pos h1, mul_zero]

end GlobalTheory.ChernReg
