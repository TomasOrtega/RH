import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
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
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
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
