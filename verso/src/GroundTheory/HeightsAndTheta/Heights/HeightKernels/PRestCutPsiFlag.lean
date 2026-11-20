import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem RestCutPsiFlag.proof : RestCutPsiFlag.Statement := by
  intro f N
  refine ⟨fun H => ?_, fun ψ P => ?_⟩
  · unfold realFlagIntegral RestTerms.flagIntegral
    push_cast [Rat.cast_sum, Rat.cast_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [coeff_map, eq_ratCast]
    ring
  · unfold realFlagIntegral RestTerms.flagIntegral
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [KRest.coeff_psiPoly]
    have h : coeff α P * ((coeff α (RestTerms.blockVandermonde f N) *
        α.prod (fun _ e => (e.factorial : ℚ)) : ℚ) : ℝ) =
        (coeff α (RestTerms.blockVandermonde f N) *
          α.prod (fun _ e => (e.factorial : ℚ))) • coeff α P := by
      rw [Rat.smul_def, mul_comm]
    rw [h, ψ.map_smul, smul_eq_mul]
    ring

end GroundTheory.Heights₂.Heights
