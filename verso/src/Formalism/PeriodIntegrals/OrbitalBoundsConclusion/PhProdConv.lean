import Mathlib
import Formalism.PeriodIntegrals.PhProdConv

/- English proof (translation)
Introduce `ι _ _ G _ _ _ _ _ _ μ _ _ _ ph m hint hconv`. Use `⟨MeasureTheory.Integrable.fintype_prod_dep hint, ?_⟩` and prove the remaining obligations. Unfold `PI.PhProdConv.PhConv`. Use `⟨?_, fun g => ?_, fun x y => ?_⟩` and prove the remaining obligations. Conclude with `Finset.prod_eq_one (fun i _ => (hconv i).1)`.

Express the relevant statement in the definitionally equal form `∏ i, ph i ((g i)⁻¹) = starRingEnd ℂ (∏ i, ph i (g i))`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_congr rfl (fun i _ => (hconv i).2.1 (g i))`. Establish `key : (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i)) = fun g => ∏ i, (fun i (h : G i) => ph i h * ph i ((x i)⁻¹ * h⁻¹ * y i)) i (g i)`. Use function extensionality and compare the values at `g`.

Rewrite using `[← Finset.prod_mul_distrib]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `MeasureTheory.Integrable (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i)) (MeasureTheory.Measure.pi μ) ∧ ∫ g, (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i)) g ∂(MeasureTheory.Measure.pi μ) = (∏ i, m i (x i)) * ∏ i, ph i (y i)`. Rewrite using `[key]`. Use `⟨MeasureTheory.Integrable.fintype_prod_dep (fun i => ((hconv i).2.2 (x i) (y i)).1), ?_⟩` and prove the remaining obligations.

Rewrite using `[MeasureTheory.integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun i (h : G i) => ph i h * ph i ((x i)⁻¹ * h⁻¹ * y i)), ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl (fun i _ => ((hconv i).2.2 (x i) (y i)).2)`.
-/
theorem isConvIdempotent_pi : PI.PhProdConv.ProdConv := by
  intro ι _ _ G _ _ _ _ _ _ μ _ _ _ ph m hint hconv
  refine ⟨MeasureTheory.Integrable.fintype_prod_dep hint, ?_⟩
  unfold PI.PhProdConv.PhConv
  refine ⟨?_, fun g => ?_, fun x y => ?_⟩
  · exact Finset.prod_eq_one (fun i _ => (hconv i).1)
  · change ∏ i, ph i ((g i)⁻¹) = starRingEnd ℂ (∏ i, ph i (g i))
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => (hconv i).2.1 (g i))
  · have key : (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i)) =
        fun g => ∏ i, (fun i (h : G i) => ph i h * ph i ((x i)⁻¹ * h⁻¹ * y i)) i (g i) := by
      funext g
      rw [← Finset.prod_mul_distrib]
      rfl
    change MeasureTheory.Integrable
        (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i))
        (MeasureTheory.Measure.pi μ) ∧
      ∫ g, (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i)) g
        ∂(MeasureTheory.Measure.pi μ) = (∏ i, m i (x i)) * ∏ i, ph i (y i)
    rw [key]
    refine ⟨MeasureTheory.Integrable.fintype_prod_dep
      (fun i => ((hconv i).2.2 (x i) (y i)).1), ?_⟩
    rw [MeasureTheory.integral_fintype_prod_eq_prod (𝕜 := ℂ)
      (fun i (h : G i) => ph i h * ph i ((x i)⁻¹ * h⁻¹ * y i)), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => ((hconv i).2.2 (x i) (y i)).2)
