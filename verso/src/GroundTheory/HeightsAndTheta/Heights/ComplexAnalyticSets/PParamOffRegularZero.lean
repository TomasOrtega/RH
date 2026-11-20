import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamOffRegularZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. It suffices to derive a contradiction.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Both sides reduce to the same expression.

Both sides reduce to the same expression. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem ParamOffRegularZero.proof : ParamOffRegularZero.Statement := by
  intro n d W A σ r N hσ hZN f φ hfN
  set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg
  set C : Set (Fin d → ℂ) := {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
      LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} with hC
  set R : Set (Fin d → ℂ) := {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
      LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} with hR
  have hgd : ∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, DifferentiableAt ℂ g w := by
    intro w hw
    have hσw : DifferentiableAt ℂ σ w := (hσ w hw).differentiableAt (Metric.isOpen_ball.mem_nhds hw)
    exact (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiableAt.comp w hσw
  have hnull : volume (g '' C) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun w => (fderiv ℂ g w).restrictScalars ℝ) ?_ ?_
    · intro w hw
      exact ((hgd w hw.1).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    · intro w hw
      rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
        LinearMap.det_restrictScalars, hw.2.2, Algebra.norm_complex_apply, map_zero]
  have hz : ∀ y ∉ g '' C, chartDens W A ((σ '' R)ᶜ.indicator f) φ y = 0 := by
    intro y hy
    unfold chartDens sheetSum
    apply finsum_eq_zero_of_forall_eq_zero
    intro x
    classical
    rw [finsum_eq_if]
    split_ifs with hx hs
    · by_cases hxR : x ∈ σ '' R
      · simp [hxR]
      by_cases hf : f x = 0
      · simp [hxR, hf]
      exfalso
      have hxN : x ∈ N := hfN (subset_tsupport f (Function.mem_support.mpr hf))
      obtain ⟨w, hw, rfl⟩ := hZN ⟨hx.1, hxN⟩
      have hdet : LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0 := by
        by_contra hne
        exact hxR ⟨w, ⟨hw, hxN, hne⟩, rfl⟩
      exact hy ⟨w, ⟨hw, hxN, hdet⟩, hx.2⟩
    · rfl
    · rfl
  unfold chartInt
  apply integral_eq_zero_of_ae
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun y hy => ?_) hnull
  by_contra h
  exact hy (by simpa using hz y h)

end

end GroundTheory.Heights₂.Heights
