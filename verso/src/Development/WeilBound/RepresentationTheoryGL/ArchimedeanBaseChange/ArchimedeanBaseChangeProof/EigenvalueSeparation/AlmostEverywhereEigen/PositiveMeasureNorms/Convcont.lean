import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf

open MeasureTheory Topology
open scoped Pointwise
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

namespace Convcont

/- English proof (translation)
Use `integral_mul_left_eq_self (μ := X.μ) (fun z => φ (x⁻¹ * z) * u z) x` as an intermediate fact. Simplify using `only [inv_mul_cancel_left] at this`. Conclude with `this`.
-/
theorem shift (X : Ctx) (φ u : X.G → ℂ) (x : X.G) :
    ∫ y, φ y * u (x * y) ∂X.μ = ∫ z, φ (x⁻¹ * z) * u z ∂X.μ := by
  have := integral_mul_left_eq_self (μ := X.μ) (fun z => φ (x⁻¹ * z) * u z) x
  simp only [inv_mul_cancel_left] at this
  exact this

end Convcont

open Convcont in
/- English proof (translation)
Introduce `X φ u hφ hu`. Establish `hfun : (fun x => ∫ y, φ y * u (x * y) ∂X.μ) = fun x => ∫ z, φ (x⁻¹ * z) * u z ∂X.μ`. Use function extensionality and compare the values at `fun x => shift X φ u x`. Rewrite using `[hfun]`. Take `⟨B, hB⟩` from `hφ.1.bounded_above_of_compact_support hφ.2`.

Use `continuous_iff_continuousAt.2 fun x₀ => ?_` and prove the remaining obligations. Take `⟨N, hNc, hN⟩` from `exists_compact_mem_nhds x₀`. Establish `hK : IsCompact (N * tsupport φ)` using `hNc.mul hφ.2`. Establish `hcx : ∀ z : X.G, Continuous fun x : X.G => φ (x⁻¹ * z)` using `fun z => hφ.1.comp (continuous_inv.mul continuous_const)`. Use `continuousAt_of_dominated (bound := (N * tsupport φ).indicator fun z => B * ‖u z‖) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Conclude with `Filter.Eventually.of_forall fun x => ((hφ.1.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mul hu.aestronglyMeasurable`. Use `filter_upwards [hN] with x hx`. Use `Filter.Eventually.of_forall fun z => ?_` and prove the remaining obligations. Distinguish the cases in `hz : z ∈ N * tsupport φ`. Rewrite using `[Set.indicator_of_mem hz, norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)`. Rewrite using `[Set.indicator_of_notMem hz]`. Establish `h0 : φ (x⁻¹ * z) = 0`. Assume the negation of the conclusion as `h`. Apply `hz` to reduce the goal to its premises.

Use `⟨x, hx, x⁻¹ * z, subset_tsupport _ h, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `[h0]`. Rewrite using `[integrable_indicator_iff hK.measurableSet]`. Conclude with `((hu.integrableOn_isCompact hK).norm.const_mul B)`.

Conclude with `Filter.Eventually.of_forall fun z => ((hcx z).mul continuous_const).continuousAt`.
-/
theorem convcont : ConvCont := by
  intro X φ u hφ hu
  have hfun : (fun x => ∫ y, φ y * u (x * y) ∂X.μ) = fun x => ∫ z, φ (x⁻¹ * z) * u z ∂X.μ :=
    funext fun x => shift X φ u x
  rw [hfun]
  obtain ⟨B, hB⟩ := hφ.1.bounded_above_of_compact_support hφ.2
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x₀
  have hK : IsCompact (N * tsupport φ) := hNc.mul hφ.2
  have hcx : ∀ z : X.G, Continuous fun x : X.G => φ (x⁻¹ * z) :=
    fun z => hφ.1.comp (continuous_inv.mul continuous_const)
  refine continuousAt_of_dominated (bound := (N * tsupport φ).indicator fun z => B * ‖u z‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((hφ.1.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mul hu.aestronglyMeasurable
  · filter_upwards [hN] with x hx
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ N * tsupport φ
    · rw [Set.indicator_of_mem hz, norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hz]
      have h0 : φ (x⁻¹ * z) = 0 := by
        by_contra h
        apply hz
        refine ⟨x, hx, x⁻¹ * z, subset_tsupport _ h, ?_⟩
        simp
      simp [h0]
  · rw [integrable_indicator_iff hK.measurableSet]
    exact ((hu.integrableOn_isCompact hK).norm.const_mul B)
  · exact Filter.Eventually.of_forall fun z => ((hcx z).mul continuous_const).continuousAt

end PositivityTheory.Rg.BcB.E2.P
