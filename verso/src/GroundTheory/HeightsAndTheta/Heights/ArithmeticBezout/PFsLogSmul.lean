import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

/- English proof (translation)
Unfold `HermNorm.dualNorm`. Rewrite using `[Matrix.mulVec_smul]`. Establish `hs : (∑ i, ‖(t • ((h.mat)ᵀ⁻¹ *ᵥ y)) i‖ ^ 2) = ‖t‖ ^ 2 * ∑ i, ‖((h.mat)ᵀ⁻¹ *ᵥ y) i‖ ^ 2`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]`. Rewrite using `[hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]`.
-/
theorem HermNorm.dualNorm_smul {n : ℕ} (h : HermNorm n) (t : ℂ) (y : Fin n → ℂ) :
    h.dualNorm (t • y) = ‖t‖ * h.dualNorm y := by
  unfold HermNorm.dualNorm
  rw [Matrix.mulVec_smul]
  have hs : (∑ i, ‖(t • ((h.mat)ᵀ⁻¹ *ᵥ y)) i‖ ^ 2) = ‖t‖ ^ 2 * ∑ i, ‖((h.mat)ᵀ⁻¹ *ᵥ y) i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/- English proof (translation)
Introduce `n h u y t ht`. Unfold `fsLog`. Establish `hp : (∑ j, u j * (t • y) j) = t * ∑ j, u j * y j`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `ht' : ‖t‖ ≠ 0` using `norm_ne_zero_iff.mpr ht`. Rewrite using `[hp, h.dualNorm_smul, norm_mul, mul_div_mul_left _ _ ht']`.
-/
theorem FsLogSmul.proof : FsLogSmul.Statement := by
  intro n h u y t ht
  unfold fsLog
  have hp : (∑ j, u j * (t • y) j) = t * ∑ j, u j * y j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    ring
  have ht' : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  rw [hp, h.dualNorm_smul, norm_mul, mul_div_mul_left _ _ ht']

end GroundTheory.Heights₂.Heights
