import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsExtraAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

/- English proof (translation)
Introduce `K _ ι _ P f g a R hP hf hg hfP hgP hR hRu`. Establish `: P.IsPrime` using `hP.2.1.1`. Take `⟨x, hx⟩` from `exists_funField_mul_eq hf hg hgP`. Take `⟨e, he⟩` from `hE K ι P R hP hR hRu`. Rewrite using `[hV K ι P f g a x hP hf hg hfP hgP hx]`.

Establish `hA : IsSectionOn P (HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun k => (a k : ℤ))) g` using `⟨a, fun _ => rfl, hg, hgP⟩`. Establish `key : ∀ t : R, Real.log ‖e t x‖ = Real.log (‖eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) f)‖ / ‖eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) g)‖)`. Introduce `t`. Establish `hg0` using `eval_ne_zero_of_dimOne arithVarZero hP hA (hR t t.2)`. Rewrite using `[← he t f g a hf hg hgP x hx, norm_mul, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hg0)]`.

Rewrite using `[← finsum_comp_equiv e, finsum_eq_sum_of_fintype, Fintype.sum_congr _ _ key]`. Conclude with `Finset.sum_coe_sort R (fun t => Real.log (‖eval t (map (Int.castRingHom ℂ) f)‖ / ‖eval t (map (Int.castRingHom ℂ) g)‖))`.
-/
theorem VerticalClosedPoints.proof (hE : regularityEmbedding_holds.Statement) (hV : VerticalEmbedding.Statement) : VerticalClosedPoints.Statement := by
  intro K _ ι _ P f g a R hP hf hg hfP hgP hR hRu
  have : P.IsPrime := hP.2.1.1
  obtain ⟨x, hx⟩ := exists_funField_mul_eq hf hg hgP
  obtain ⟨e, he⟩ := hE K ι P R hP hR hRu
  rw [hV K ι P f g a x hP hf hg hfP hgP hx]
  have hA : IsSectionOn P (HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun k => (a k : ℤ))) g :=
    ⟨a, fun _ => rfl, hg, hgP⟩
  have key : ∀ t : R, Real.log ‖e t x‖ =
      Real.log (‖eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) f)‖ /
        ‖eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) g)‖) := by
    intro t
    have hg0 := eval_ne_zero_of_dimOne arithVarZero hP hA (hR t t.2)
    rw [← he t f g a hf hg hgP x hx, norm_mul, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hg0)]
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype, Fintype.sum_congr _ _ key]
  exact Finset.sum_coe_sort R (fun t => Real.log (‖eval t (map (Int.castRingHom ℂ) f)‖ /
    ‖eval t (map (Int.castRingHom ℂ) g)‖))

end

end GroundTheory.Heights₂.Heights.Inter
