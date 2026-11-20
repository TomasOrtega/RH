import Mathlib

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TopClm

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/- English proof (translation)
The claim follows from `A.opNorm_le_bound zero_le_one fun v => by rw [hA, one_mul]`.
-/
theorem opNorm_le_one_of_isometry (A : V →L[ℂ] V) (hA : ∀ v, ‖A v‖ = ‖v‖) : ‖A‖ ≤ 1 := A.opNorm_le_bound zero_le_one fun v => by rw [hA, one_mul]

/- English proof (translation)
Introduce `h0`. Apply `h` to reduce the goal to its premises. Establish `hξ : ξ ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h`.

Establish `hξn : ‖ξ‖ ≠ 0` using `norm_ne_zero_iff.2 hξ`. Distinguish the cases in `hint : Integrable (fun p => s p • A p) μ`. Establish `h1` using `ContinuousLinearMap.integral_apply hint ξ`. Rewrite `h1` using `[h0]`. Simplify using `using h1.symm`.

Apply `integral_undef` to reduce the goal to its premises. Introduce `hint2`. Apply `hint` to reduce the goal to its premises. Establish `hAξ : AEStronglyMeasurable (fun p => A p ξ) μ` using `(ContinuousLinearMap.apply ℂ V ξ).continuous.comp_aestronglyMeasurable hA`. Establish `hnC : ((‖ξ‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hξn`.

Establish `hs : AEStronglyMeasurable s μ`. Establish `h1 : AEStronglyMeasurable (fun p => ⟪A p ξ, s p • A p ξ⟫_ℂ / (((‖ξ‖ : ℝ) : ℂ) ^ 2)) μ` using `(continuous_id.div_const (((‖ξ‖ : ℝ) : ℂ) ^ 2)).comp_aestronglyMeasurable (hAξ.inner hint2.aestronglyMeasurable)`. Use `h1.congr ?_` and prove the remaining obligations. Use `filter_upwards [hu] with p hp`. Rewrite using `[inner_smul_right, inner_self_eq_norm_sq_to_K, hp ξ]`.

Use `first`. Consider the case `(field_simp; done)`. Consider the case `(field_simp; rfl)`. Consider the case `(rw [mul_div_assoc, div_self (pow_ne_zero _ hnC), mul_one])`. Use `Integrable.mono' (g := fun p => ‖ξ‖⁻¹ * ‖s p • A p ξ‖) (hint2.norm.const_mul _) (hs.smul hA) ?_` and prove the remaining obligations.

Use `filter_upwards [hu] with p hp`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_smul, hp ξ]`. Clear the denominators using the available nonvanishing facts.
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
