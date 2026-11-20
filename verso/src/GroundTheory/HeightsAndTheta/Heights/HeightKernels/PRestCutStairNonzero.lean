import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Unfold `RestTerms.flagIntegral`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_sub, coeff_C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem flagIntegral_sub_C_mul (f N : ℕ) (H S : RestTerms.RootRing f N) (b : ℚ) :
    RestTerms.flagIntegral f N (H - C b * S) =
      RestTerms.flagIntegral f N H - b * RestTerms.flagIntegral f N S := by
  unfold RestTerms.flagIntegral
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_sub, coeff_C_mul]
  ring

/- English proof (translation)
Introduce `f N H hH hne hstair`. Take `⟨b, hb⟩` from `h₁ f N H hH`. Establish `hmem : H - C b * restStair f N ∈ restPsumIdeal f N` using `hb`. Establish `h0` using `h₂ f N _ hmem`. Rewrite `h0` using `[flagIntegral_sub_C_mul, hstair, mul_zero, sub_zero]`.

Conclude with `hne h0`.
-/
theorem RestCutStairNonzero.proof (h₁ : RestTerms.CoinvariantTopDegree.Statement)
    (h₂ : RestCutFlagKillsIdeal.Statement) : RestCutStairNonzero.Statement := by
  intro f N H hH hne hstair
  obtain ⟨b, hb⟩ := h₁ f N H hH
  have hmem : H - C b * restStair f N ∈ restPsumIdeal f N := hb
  have h0 := h₂ f N _ hmem
  rw [flagIntegral_sub_C_mul, hstair, mul_zero, sub_zero] at h0
  exact hne h0

end GroundTheory.Heights₂.Heights
