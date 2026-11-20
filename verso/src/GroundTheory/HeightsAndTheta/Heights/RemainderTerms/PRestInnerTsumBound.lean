import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsElem
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Elementary
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Check the signs of the components of the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem RestInnerTsumBound.proof : RestInnerTsumBound.Statement := by
  intro p k c M hp hk hc
  obtain ⟨hsum, hle⟩ := GeometricTail.intersectionNumber_baseChange p k hp hk
  have hM : 0 ≤ M := (abs_nonneg (c 0)).trans (hc 0)
  have hnn : ∀ n : ℕ, 0 ≤ (p ^ ((n + 1) * k))⁻¹ := fun n => by
    have : (0 : ℝ) ≤ p := by linarith
    positivity
  have hbound : ∀ n : ℕ, ‖(p ^ ((n + 1) * k))⁻¹ * c n‖ ≤ (p ^ ((n + 1) * k))⁻¹ * M := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn n)]
    exact mul_le_mul_of_nonneg_left (hc n) (hnn n)
  have hsumM : Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * M) := hsum.mul_right M
  have hS : Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * c n) :=
    Summable.of_norm_bounded hsumM hbound
  refine ⟨hS, ?_⟩
  calc |∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * c n|
      = ‖∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * c n‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖(p ^ ((n + 1) * k))⁻¹ * c n‖ := norm_tsum_le_tsum_norm hS.norm
    _ ≤ ∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * M := hS.norm.tsum_le_tsum hbound hsumM
    _ = (∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹) * M := tsum_mul_right
    _ ≤ (2 * (p ^ k)⁻¹) * M := mul_le_mul_of_nonneg_right hle hM
    _ = M * (2 * (p ^ k)⁻¹) := mul_comm _ _

end RestTerms

end GroundTheory.Heights₂.Heights
