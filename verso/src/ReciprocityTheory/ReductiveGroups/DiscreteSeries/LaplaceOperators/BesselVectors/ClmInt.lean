import Mathlib

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TopClm

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem opNorm_le_one_of_isometry (A : V →L[ℂ] V) (hA : ∀ v, ‖A v‖ = ‖v‖) : ‖A‖ ≤ 1 := A.opNorm_le_bound zero_le_one fun v => by rw [hA, one_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Treat this case separately.

Treat this case separately. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. A detailed English derivation is pending.
-/
theorem integral_ne_zero_of_apply (s : α → ℂ) (A : α → V →L[ℂ] V) (hA : AEStronglyMeasurable A μ)
    (hu : ∀ᵐ p ∂μ, ∀ v, ‖A p v‖ = ‖v‖) (ξ : V) (h : ∫ p, s p • A p ξ ∂μ ≠ 0) :
    ∫ p, s p • A p ∂μ ≠ 0 := by
  intro h0
  apply h
  have hξ : ξ ≠ 0 := by
    rintro rfl
    simp at h
  have hξn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
  by_cases hint : Integrable (fun p => s p • A p) μ
  · have h1 := ContinuousLinearMap.integral_apply hint ξ
    rw [h0] at h1
    simpa using h1.symm
  · apply integral_undef
    intro hint2
    apply hint
    have hAξ : AEStronglyMeasurable (fun p => A p ξ) μ :=
      (ContinuousLinearMap.apply ℂ V ξ).continuous.comp_aestronglyMeasurable hA
    have hnC : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hξn
    have hs : AEStronglyMeasurable s μ := by
      have h1 : AEStronglyMeasurable
          (fun p => ⟪A p ξ, s p • A p ξ⟫_ℂ / (((‖ξ‖ : ℝ) : ℂ) ^ 2)) μ :=
        (continuous_id.div_const (((‖ξ‖ : ℝ) : ℂ) ^ 2)).comp_aestronglyMeasurable
          (hAξ.inner hint2.aestronglyMeasurable)
      refine h1.congr ?_
      filter_upwards [hu] with p hp
      rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hp ξ]
      first
      | (field_simp; done)
      | (field_simp; rfl)
      | (rw [mul_div_assoc, div_self (pow_ne_zero _ hnC), mul_one])
    refine Integrable.mono' (g := fun p => ‖ξ‖⁻¹ * ‖s p • A p ξ‖) (hint2.norm.const_mul _)
      (hs.smul hA) ?_
    filter_upwards [hu] with p hp
    calc ‖s p • A p‖ ≤ ‖s p‖ * ‖A p‖ := norm_smul_le _ _
      _ ≤ ‖s p‖ * 1 := mul_le_mul_of_nonneg_left (opNorm_le_one_of_isometry _ hp) (norm_nonneg _)
      _ = ‖ξ‖⁻¹ * ‖s p • A p ξ‖ := by
        rw [norm_smul, hp ξ]
        field_simp

end ReciprocityTheory.ChartRestriction.DS.Lap.TopClm
