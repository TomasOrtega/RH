import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory

noncomputable section

def IntervalMomentsDetermine.Statement : Prop :=
  ∀ μ ν : Measure ℝ, IsFiniteMeasure μ → IsFiniteMeasure ν →
    μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → ν (Set.Icc (-1 : ℝ) 1)ᶜ = 0 →
    (∀ k : ℕ, ∫ x, x ^ k ∂μ = ∫ x, x ^ k ∂ν) → μ = ν

/- English proof (translation)
Use `⟨inferInstance, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.dirac_apply' _ (measurableSet_Icc.compl)]`. Simplify using the standard rewrite rules. Conclude with `⟨by simp [ENNReal.mul_lt_top]⟩`. Simplify using `[Measure.restrict_apply measurableSet_Icc.compl]`.
-/
example : IsFiniteMeasure (Measure.dirac (0 : ℝ)) ∧ Measure.dirac (0 : ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0 ∧
    IsFiniteMeasure ((2⁻¹ : ENNReal) • (volume : Measure ℝ).restrict (Set.Icc (-1) 1)) ∧
    ((2⁻¹ : ENNReal) • (volume : Measure ℝ).restrict (Set.Icc (-1) 1)) (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.dirac_apply' _ (measurableSet_Icc.compl)]
    simp
  · exact ⟨by simp [ENNReal.mul_lt_top]⟩
  · simp [Measure.restrict_apply measurableSet_Icc.compl]

end

end GroundTheory.Heights₂.Heights.FlagBundles
