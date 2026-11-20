import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
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
