import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Introduce `f N`. Use `⟨fun H => ?_, fun ψ P => ?_⟩` and prove the remaining obligations. Unfold `realFlagIntegral RestTerms.flagIntegral`. Move the coercions through the operations in `[Rat.cast_sum, Rat.cast_mul]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations.

Rewrite using `[coeff_map, eq_ratCast]`. Expand and normalize the polynomial expressions, which then agree. Unfold `realFlagIntegral RestTerms.flagIntegral`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations.

Rewrite using `[KRest.coeff_psiPoly]`. Establish `h : coeff α P * ((coeff α (RestTerms.blockVandermonde f N) * α.prod (fun _ e => (e.factorial : ℚ)) : ℚ) : ℝ) = (coeff α (RestTerms.blockVandermonde f N) * α.prod (fun _ e => (e.factorial : ℚ))) • coeff α P`. Rewrite using `[Rat.smul_def, mul_comm]`. Rewrite using `[h, ψ.map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
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
