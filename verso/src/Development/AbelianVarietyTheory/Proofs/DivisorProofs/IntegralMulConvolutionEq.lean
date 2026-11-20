import Mathlib
open MeasureTheory Pointwise

namespace GlobalTheory

/- English proof (translation)
Use `haveI := hμ`. Establish `hC : IsCompact (tsupport κ)` using `hκc`. Take `⟨M, hM⟩ : ∃ M, ∀ w ∈ tsupport κ * K, ‖f w‖ ≤ M` from `(hC.mul hK).exists_bound_of_continuousOn hf.continuousOn`. Use `set G : H × H → ℂ := fun p => κ p.1 * (f p.2 * a (p.1⁻¹ * p.2)) with hG`. Establish `hGm : AEStronglyMeasurable G (μ.prod μ)`.

Establish `h1 : Measurable fun p : H × H => a (p.1⁻¹ * p.2)` using `ha.comp (measurable_fst.inv.mul measurable_snd)`. Conclude with `(hκ.comp continuous_fst).aestronglyMeasurable.mul ((hf.comp continuous_snd).aestronglyMeasurable.mul h1.aestronglyMeasurable)`. Establish `hbound : Integrable (fun p : H × H => (‖κ p.1‖ * M) * ‖a p.2‖) (μ.prod μ)` using `Integrable.mul_prod ((hκ.integrable_of_hasCompactSupport hκc).norm.mul_const M) hai.norm`. Establish `hGs : Integrable (G ∘ fun p : H × H => (p.1, p.1 * p.2)) (μ.prod μ)`. Use `hbound.mono' (hGm.comp_measurePreserving (measurePreserving_prod_mul μ μ)) ?_` and prove the remaining obligations.

Use `Filter.Eventually.of_forall fun p => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, G, inv_mul_cancel_left]`. Distinguish the cases in `h1 : κ p.1 = 0`. Simplify using `only [h1, zero_mul, norm_zero, mul_zero]`. Check the signs of the components of the expression.

Distinguish the cases in `h2 : a p.2 = 0`. Simplify using `only [h2, mul_zero, norm_zero]`. Both sides reduce to the same expression. Establish `hx : p.1 ∈ tsupport κ` using `subset_tsupport _ h1`. Establish `hy : p.2 ∈ K`.

Assume the negation of the conclusion as `h`. Conclude with `h2 (haK _ h)`. Establish `hfM` using `hM _ (Set.mul_mem_mul hx hy)`. Rewrite using `[norm_mul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hGi : Integrable G (μ.prod μ)` using `((measurePreserving_prod_mul μ μ).integrable_comp hGm).1 hGs`. Establish `hF : Integrable (Function.uncurry fun z x => f z * (κ x * a (x⁻¹ * z))) (μ.prod μ)`. Use `hGi.swap.congr (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp, G, Prod.fst_swap, Prod.snd_swap, Function.uncurry]`. Expand and normalize the polynomial expressions, which then agree.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `z`. Conclude with `(integral_const_mul _ _).symm`. Use `_ = ∫ x, ∫ z, f z * (κ x * a (x⁻¹ * z)) ∂μ ∂μ := integral_integral_swap hF`.

Use `_ = ∫ x, κ x * ∫ y, f (x * y) * a y ∂μ ∂μ := by`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[← integral_mul_left_eq_self (fun z => f z * (κ x * a (x⁻¹ * z))) x, ← integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `y`. Simplify using `only [inv_mul_cancel_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_mul_convolution_eq (H : Type) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] (μ : Measure H) (hμ : μ.IsHaarMeasure)
    (K : Set H) (hK : IsCompact K) (κ a : H → ℂ) (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) (ha : Measurable a) (hai : Integrable a μ)
    (haK : ∀ x ∉ K, a x = 0) (f : H → ℂ) (hf : Continuous f) :
    ∫ z, f z * (∫ x, κ x * a (x⁻¹ * z) ∂μ) ∂μ = ∫ x, κ x * ∫ y, f (x * y) * a y ∂μ ∂μ := by
  haveI := hμ
  have hC : IsCompact (tsupport κ) := hκc
  obtain ⟨M, hM⟩ : ∃ M, ∀ w ∈ tsupport κ * K, ‖f w‖ ≤ M :=
    (hC.mul hK).exists_bound_of_continuousOn hf.continuousOn
  set G : H × H → ℂ := fun p => κ p.1 * (f p.2 * a (p.1⁻¹ * p.2)) with hG
  have hGm : AEStronglyMeasurable G (μ.prod μ) := by
    have h1 : Measurable fun p : H × H => a (p.1⁻¹ * p.2) :=
      ha.comp (measurable_fst.inv.mul measurable_snd)
    exact (hκ.comp continuous_fst).aestronglyMeasurable.mul
      ((hf.comp continuous_snd).aestronglyMeasurable.mul h1.aestronglyMeasurable)
  have hbound : Integrable (fun p : H × H => (‖κ p.1‖ * M) * ‖a p.2‖) (μ.prod μ) :=
    Integrable.mul_prod ((hκ.integrable_of_hasCompactSupport hκc).norm.mul_const M) hai.norm
  have hGs : Integrable (G ∘ fun p : H × H => (p.1, p.1 * p.2)) (μ.prod μ) := by
    refine hbound.mono' (hGm.comp_measurePreserving (measurePreserving_prod_mul μ μ)) ?_
    refine Filter.Eventually.of_forall fun p => ?_
    simp only [Function.comp, G, inv_mul_cancel_left]
    by_cases h1 : κ p.1 = 0
    · simp only [h1, zero_mul, norm_zero, mul_zero]; positivity
    by_cases h2 : a p.2 = 0
    · simp only [h2, mul_zero, norm_zero]; rfl
    have hx : p.1 ∈ tsupport κ := subset_tsupport _ h1
    have hy : p.2 ∈ K := by
      by_contra h; exact h2 (haK _ h)
    have hfM := hM _ (Set.mul_mem_mul hx hy)
    rw [norm_mul, norm_mul]
    calc ‖κ p.1‖ * (‖f (p.1 * p.2)‖ * ‖a p.2‖) ≤ ‖κ p.1‖ * (M * ‖a p.2‖) := by gcongr
      _ = ‖κ p.1‖ * M * ‖a p.2‖ := by ring
  have hGi : Integrable G (μ.prod μ) :=
    ((measurePreserving_prod_mul μ μ).integrable_comp hGm).1 hGs
  have hF : Integrable (Function.uncurry fun z x => f z * (κ x * a (x⁻¹ * z))) (μ.prod μ) := by
    refine hGi.swap.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp, G, Prod.fst_swap, Prod.snd_swap, Function.uncurry]
    ring
  calc ∫ z, f z * (∫ x, κ x * a (x⁻¹ * z) ∂μ) ∂μ
      = ∫ z, ∫ x, f z * (κ x * a (x⁻¹ * z)) ∂μ ∂μ := by
        congr 1; funext z; exact (integral_const_mul _ _).symm
    _ = ∫ x, ∫ z, f z * (κ x * a (x⁻¹ * z)) ∂μ ∂μ := integral_integral_swap hF
    _ = ∫ x, κ x * ∫ y, f (x * y) * a y ∂μ ∂μ := by
        congr 1; funext x
        rw [← integral_mul_left_eq_self (fun z => f z * (κ x * a (x⁻¹ * z))) x,
          ← integral_const_mul]
        congr 1; funext y
        simp only [inv_mul_cancel_left]
        ring

end GlobalTheory
