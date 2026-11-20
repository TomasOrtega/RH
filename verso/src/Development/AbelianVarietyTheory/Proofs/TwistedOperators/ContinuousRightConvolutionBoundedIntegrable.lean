import Mathlib

open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Use `continuous_of_dominated (bound := fun h => B * ‖α h‖) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `x`. Use `hα.aestronglyMeasurable.mul ?_` and prove the remaining obligations. Conclude with `(hφ.comp (continuous_const.mul continuous_subtype_val)).aestronglyMeasurable`. Introduce `x`.

Use `Filter.Eventually.of_forall (fun h => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, mul_comm]`. Conclude with `mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)`. Conclude with `hα.norm.const_mul B`. Use `Filter.Eventually.of_forall (fun h => ?_)` and prove the remaining obligations.

Conclude with `continuous_const.mul (hφ.comp (continuous_id.mul continuous_const))`.
-/
theorem conv_right_continuous {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (m : Measure H) (α : H → ℂ) (hα : Integrable α m) (φ : G → ℂ) (hφ : Continuous φ)
    (B : ℝ) (hB : ∀ g, ‖φ g‖ ≤ B) :
    Continuous (fun x => ∫ h, α h * φ (x * (h : G)) ∂m) := by
  refine continuous_of_dominated (bound := fun h => B * ‖α h‖) ?_ ?_ ?_ ?_
  · intro x
    refine hα.aestronglyMeasurable.mul ?_
    exact (hφ.comp (continuous_const.mul continuous_subtype_val)).aestronglyMeasurable
  · intro x
    refine Filter.Eventually.of_forall (fun h => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  · exact hα.norm.const_mul B
  · refine Filter.Eventually.of_forall (fun h => ?_)
    exact continuous_const.mul (hφ.comp (continuous_id.mul continuous_const))

end GlobalTheory
