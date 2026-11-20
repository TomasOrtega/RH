import Mathlib

open MeasureTheory in
/- English proof (translation)
Rewrite using `[integral_map hX.aemeasurable hG.aestronglyMeasurable]`. Establish `h : AEMeasurable (fun ω ↦ (f ω).toNNReal) ν` using `hf.aemeasurable.real_toNNReal`. Establish `h2` using `integral_withDensity_eq_integral_smul₀ h (fun ω ↦ G (X ω))`. Use `Eq.trans h2 ?_` and prove the remaining obligations. Use `integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)` and prove the remaining obligations.

Simplify using `only [NNReal.smul_def, Real.coe_toNNReal', Complex.real_smul, mul_comm]`.
-/
private theorem UpperTheory.Reformulated.B.Qh3.one_side {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (G : (ι → ℝ) → ℂ) (hG : Measurable G) :
    ∫ x, G x ∂Measure.map X (ν.withDensity fun ω ↦ ENNReal.ofReal (f ω)) =
      ∫ ω, G (X ω) * ((max (f ω) 0 : ℝ) : ℂ) ∂ν := by
  rw [integral_map hX.aemeasurable hG.aestronglyMeasurable]
  have h : AEMeasurable (fun ω ↦ (f ω).toNNReal) ν := hf.aemeasurable.real_toNNReal
  have h2 := integral_withDensity_eq_integral_smul₀ h (fun ω ↦ G (X ω))
  refine Eq.trans h2 ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal', Complex.real_smul, mul_comm]

open MeasureTheory in
/- English proof (translation)
Establish `h1 : Integrable (fun ω ↦ ((max (f ω) 0 : ℝ) : ℂ)) ν` using `hf.pos_part.ofReal`. Conclude with `h1.bdd_mul (c := 1) (hG.comp hX).aestronglyMeasurable (Filter.Eventually.of_forall fun ω ↦ hb _)`.
-/
private theorem UpperTheory.Reformulated.B.Qh3.int_mul {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (G : (ι → ℝ) → ℂ) (hG : Measurable G) (hb : ∀ x, ‖G x‖ ≤ (1 : ℝ)) :
    Integrable (fun ω ↦ G (X ω) * ((max (f ω) 0 : ℝ) : ℂ)) ν := by
  have h1 : Integrable (fun ω ↦ ((max (f ω) 0 : ℝ) : ℂ)) ν := hf.pos_part.ofReal
  exact h1.bdd_mul (c := 1) (hG.comp hX).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ hb _)

/- English proof (translation)
Introduce `Ω ι _ _ ν X f hX hf G hG hb`. Establish `hn : MeasureTheory.Integrable (fun ω ↦ -f ω) ν` using `hf.neg`. Rewrite using `[UpperTheory.Reformulated.B.Qh3.one_side ν X f hX hf G hG, UpperTheory.Reformulated.B.Qh3.one_side ν X (fun ω ↦ -f ω) hX hn G hG, ← MeasureTheory.integral_sub (UpperTheory.Reformulated.B.Qh3.int_mul ν X f hX hf G hG hb) (UpperTheory.Reformulated.B.Qh3.int_mul ν X (fun ω ↦ -f ω) h …`. Use `MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)` and prove the remaining obligations. Establish `h : max (f ω) 0 - max (-f ω) 0 = f ω` using `max_zero_sub_max_neg_zero_eq_self (f ω)`.

Simplify using `only`. Rewrite using `[← mul_sub, ← Complex.ofReal_sub, h]`.
-/
theorem UpperTheory.Reformulated.B.Qh3.real_diff :
    ∀ {Ω ι : Type} [inst : MeasurableSpace Ω] [Fintype ι]
    (ν : MeasureTheory.Measure Ω) (X : Ω → ι → ℝ) (f : Ω → ℝ),
    Measurable X →
      MeasureTheory.Integrable f ν →
        ∀ (G : (ι → ℝ) → ℂ),
          Measurable G →
            (∀ (x : ι → ℝ), ‖G x‖ ≤ (1 : ℝ)) →
              ∫ (x : ι → ℝ), G x ∂MeasureTheory.Measure.map X (ν.withDensity fun (ω : Ω) ↦ ENNReal.ofReal (f ω)) -
                  ∫ (x : ι → ℝ), G x ∂MeasureTheory.Measure.map X (ν.withDensity fun (ω : Ω) ↦ ENNReal.ofReal (-f ω)) =
                ∫ (ω : Ω), G (X ω) * (↑(f ω) : ℂ) ∂ν := by
  intro Ω ι _ _ ν X f hX hf G hG hb
  have hn : MeasureTheory.Integrable (fun ω ↦ -f ω) ν := hf.neg
  rw [UpperTheory.Reformulated.B.Qh3.one_side ν X f hX hf G hG,
    UpperTheory.Reformulated.B.Qh3.one_side ν X (fun ω ↦ -f ω) hX hn G hG,
    ← MeasureTheory.integral_sub (UpperTheory.Reformulated.B.Qh3.int_mul ν X f hX hf G hG hb)
      (UpperTheory.Reformulated.B.Qh3.int_mul ν X (fun ω ↦ -f ω) hX hn G hG hb)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  have h : max (f ω) 0 - max (-f ω) 0 = f ω := max_zero_sub_max_neg_zero_eq_self (f ω)
  simp only
  rw [← mul_sub, ← Complex.ofReal_sub, h]
