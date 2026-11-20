import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace PGaussDetFactor

/- English proof (translation)
Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hd.le]`. Evaluate the numerical expressions. Conclude with `Real.rpow_neg_one d`.
-/
lemma rpow_neg_half_sq {d : ℝ} (hd : 0 < d) : (d ^ (-(1 / 2 : ℝ))) ^ 2 = d⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
  norm_num
  exact Real.rpow_neg_one d

end PGaussDetFactor

open PGaussDetFactor in

/- English proof (translation)
Introduce `g Y B hY hBY`. Establish `hd : 0 < Y.det` using `hY.det_pos`. Establish `hsq : B.det ^ 2 = (1 / 2 : ℝ) ^ g * Y.det`. Use `congrArg Matrix.det hBY` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin]`.

Rewrite using `[sq]`. Conclude with `this`. Establish `hB0 : 0 < |B.det|`. Establish `: B.det ^ 2 ≠ 0` using `by rw [hsq]; positivity`. Conclude with `abs_pos.mpr (fun h => this (by rw [h]; ring))`.

Establish `hL : 0 ≤ |B.det|⁻¹` using `(inv_pos.mpr hB0).le`. Establish `hR : 0 ≤ √2 ^ g * Y.det ^ (-(1 / 2 : ℝ))` using `by positivity`. Use `(pow_left_inj₀ hL hR (two_ne_zero)).mp ?_` and prove the remaining obligations. Rewrite using `[inv_pow, sq_abs, hsq, mul_pow, rpow_neg_half_sq hd, ← pow_mul, mul_comm g 2, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]`. Rewrite using `[mul_inv, one_div, inv_pow, inv_inv]`.
-/
theorem GaussDetFactor.proof : GaussDetFactor.Statement := by
  intro g Y B hY hBY
  have hd : 0 < Y.det := hY.det_pos
  have hsq : B.det ^ 2 = (1 / 2 : ℝ) ^ g * Y.det := by
    have := congrArg Matrix.det hBY
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin] at this
    rw [sq]; exact this
  have hB0 : 0 < |B.det| := by
    have : B.det ^ 2 ≠ 0 := by rw [hsq]; positivity
    exact abs_pos.mpr (fun h => this (by rw [h]; ring))
  have hL : 0 ≤ |B.det|⁻¹ := (inv_pos.mpr hB0).le
  have hR : 0 ≤ √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) := by positivity
  refine (pow_left_inj₀ hL hR (two_ne_zero)).mp ?_
  rw [inv_pow, sq_abs, hsq, mul_pow, rpow_neg_half_sq hd, ← pow_mul, mul_comm g 2, pow_mul,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [mul_inv, one_div, inv_pow, inv_inv]

end GroundTheory.Heights₂.Heights
