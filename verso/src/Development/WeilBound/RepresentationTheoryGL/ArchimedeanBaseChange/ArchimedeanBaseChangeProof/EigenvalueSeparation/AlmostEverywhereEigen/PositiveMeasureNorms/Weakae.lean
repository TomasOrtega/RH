import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf

open MeasureTheory
open scoped ENNReal ComplexConjugate

open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

namespace Weakae

variable {Y S : Type} [MeasurableSpace Y] [MeasurableSpace S]

/- English proof (translation)
Rewrite using `[← eLpNorm_one_eq_lintegral_enorm, eLpNorm_congr_ae hf, Lp.enorm_def]`. Use `eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (μ := ν) (f := (F : S → ℂ)) (by norm_num) (Lp.aestronglyMeasurable F)` as an intermediate fact. Use `this using 3` and compare the differences between its conclusion and the goal. Evaluate the numerical expressions.
-/
theorem lint_slice (ν : Measure S) [IsFiniteMeasure ν] (F : Lp ℂ 2 ν) (f : S → ℂ) (hf : f =ᵐ[ν] F) :
    ∫⁻ s, ‖f s‖ₑ ∂ν ≤ ‖F‖ₑ * ν Set.univ ^ (1 / 2 : ℝ) := by
  rw [← eLpNorm_one_eq_lintegral_enorm, eLpNorm_congr_ae hf, Lp.enorm_def]
  have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (μ := ν) (f := (F : S → ℂ))
    (by norm_num) (Lp.aestronglyMeasurable F)
  convert this using 3
  norm_num

/- English proof (translation)
Establish `hcm : AEStronglyMeasurable (fun p : Y × S => c p.1) (m.prod ν)` using `hc.comp_fst`. Establish `hfm : AEStronglyMeasurable (fun p : Y × S => conj (f p.1 p.2)) (m.prod ν)` using `(Complex.continuous_conj.measurable.comp hf.1).aestronglyMeasurable`. Use `⟨hcm.mul hfm, ?_⟩` and prove the remaining obligations. Use `show ∫⁻ p, ‖c p.1 * conj (f p.1 p.2)‖ₑ ∂(m.prod ν) < ⊤`. Establish `hm : AEMeasurable (fun p : Y × S => ‖c p.1 * conj (f p.1 p.2)‖ₑ) (m.prod ν)` using `(hcm.mul hfm).enorm`.

Rewrite using `[lintegral_prod _ hm]`. Establish `hC : ν Set.univ ^ (1 / 2 : ℝ) ≠ ⊤` using `ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top ν _)`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Rewrite using `[← lintegral_const_mul' _ _ enorm_ne_top]`.

Use `lintegral_congr fun s => ?_` and prove the remaining obligations. Simplify using `[enorm_mul]`. Use `_ ≤ ∫⁻ y, ‖c y‖ₑ * (‖F y‖ₑ * ν Set.univ ^ (1 / 2 : ℝ)) ∂m := by`. Use `lintegral_mono fun y => ?_` and prove the remaining obligations. Use `gcongr`.

Conclude with `lint_slice ν (F y) (f y) (hf.2 y)`. Use `_ = (∫⁻ y, ‖c y‖ₑ * ‖F y‖ₑ ∂m) * ν Set.univ ^ (1 / 2 : ℝ) := by`. Repeatedly rewrite using `[← mul_assoc]`. Conclude with `lintegral_mul_const' _ _ hC`. Use `_ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hint) (lt_top_iff_ne_top.2 hC)`.
-/
theorem integrable_k (m : Measure Y) [SFinite m] (ν : Measure S) [IsFiniteMeasure ν]
    (F : Y → Lp ℂ 2 ν) (f : Y → S → ℂ) (c : Y → ℂ) (hf : IsRep F f) (hc : AEStronglyMeasurable c m)
    (hint : ∫⁻ y, ‖c y‖ₑ * ‖F y‖ₑ ∂m ≠ ⊤) :
    Integrable (fun p : Y × S => c p.1 * conj (f p.1 p.2)) (m.prod ν) := by
  have hcm : AEStronglyMeasurable (fun p : Y × S => c p.1) (m.prod ν) := hc.comp_fst
  have hfm : AEStronglyMeasurable (fun p : Y × S => conj (f p.1 p.2)) (m.prod ν) :=
    (Complex.continuous_conj.measurable.comp hf.1).aestronglyMeasurable
  refine ⟨hcm.mul hfm, ?_⟩
  show ∫⁻ p, ‖c p.1 * conj (f p.1 p.2)‖ₑ ∂(m.prod ν) < ⊤
  have hm : AEMeasurable (fun p : Y × S => ‖c p.1 * conj (f p.1 p.2)‖ₑ) (m.prod ν) :=
    (hcm.mul hfm).enorm
  rw [lintegral_prod _ hm]
  have hC : ν Set.univ ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top ν _)
  calc ∫⁻ y, ∫⁻ s, ‖c (y, s).1 * conj (f (y, s).1 (y, s).2)‖ₑ ∂ν ∂m
      = ∫⁻ y, ‖c y‖ₑ * ∫⁻ s, ‖f y s‖ₑ ∂ν ∂m := by
        refine lintegral_congr fun y => ?_
        rw [← lintegral_const_mul' _ _ enorm_ne_top]
        refine lintegral_congr fun s => ?_
        simp [enorm_mul]
    _ ≤ ∫⁻ y, ‖c y‖ₑ * (‖F y‖ₑ * ν Set.univ ^ (1 / 2 : ℝ)) ∂m := by
        refine lintegral_mono fun y => ?_
        gcongr
        exact lint_slice ν (F y) (f y) (hf.2 y)
    _ = (∫⁻ y, ‖c y‖ₑ * ‖F y‖ₑ ∂m) * ν Set.univ ^ (1 / 2 : ℝ) := by
        simp_rw [← mul_assoc]
        exact lintegral_mul_const' _ _ hC
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hint) (lt_top_iff_ne_top.2 hC)

/- English proof (translation)
Rewrite using `[← inner_conj_symm, L2.inner_indicatorConstLp_one, integral_conj]`. Use `congr 1`. Conclude with `integral_congr_ae (ae_restrict_of_ae (hf.mono fun s hs => hs.symm))`.
-/
theorem inner_ind (ν : Measure S) [IsFiniteMeasure ν] (F : Lp ℂ 2 ν) (f : S → ℂ) (hf : f =ᵐ[ν] F)
    (A : Set S) (hA : MeasurableSet A) (hνA : ν A ≠ ⊤) :
    inner ℂ F (indicatorConstLp 2 hA hνA (1 : ℂ)) = ∫ s in A, conj (f s) ∂ν := by
  rw [← inner_conj_symm, L2.inner_indicatorConstLp_one, integral_conj]
  congr 1
  exact integral_congr_ae (ae_restrict_of_ae (hf.mono fun s hs => hs.symm))

end Weakae

open Weakae in
/- English proof (translation)
Introduce `Y S ι _ _ _ m _ ν _ F f c q hf hc hint hq hw`. Establish `hki : ∀ j, Integrable (fun p : Y × S => c j p.1 * conj (f j p.1 p.2)) (m.prod ν)` using `fun j => integrable_k m ν (F j) (f j) (c j) (hf j) (hc j) (hint j)`. Establish `hGj : ∀ j, Integrable (fun s => ∫ y, c j y * conj (f j y s) ∂m) ν` using `fun j => (hki j).integral_prod_right`. Establish `hG : Integrable (fun s => ∑ j, ∫ y, c j y * conj (f j y s) ∂m) ν` using `integrable_finsetSum _ fun j _ => hGj j`. Establish `hq' : Integrable q ν` using `hq.integrable (by norm_num)`.

Use `Integrable.ae_eq_of_forall_setIntegral_eq _ _ hG hq' fun A hA hνA => ?_` and prove the remaining obligations. Establish `hR : ∫ s, q s * (indicatorConstLp 2 hA hνA.ne (1 : ℂ)) s ∂ν = ∫ s in A, q s ∂ν`. Rewrite using `[← integral_indicator hA]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hνA.ne) (c := (1 : ℂ))] with s hs`.

Rewrite using `[hs]`. Apply the tactic sequence `by_cases h : s ∈ A <;> simp [h]`. Rewrite using `[← hR, ← hw, integral_finsetSum _ fun j _ => (hGj j).integrableOn]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hres : m.prod (ν.restrict A) = (m.prod ν).restrict (Set.univ ×ˢ A)`.

Rewrite using `[← Measure.prod_restrict, Measure.restrict_univ]`. Establish `hkA : Integrable (Function.uncurry fun y s => c j y * conj (f j y s)) (m.prod (ν.restrict A))`. Rewrite using `[hres]`. Conclude with `(hki j).restrict`. Use `symm`.

Combine the equalities or inequalities in the displayed calculation. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[inner_ind ν (F j y) (f j y) ((hf j).2 y) A hA hνA.ne, integral_const_mul]`. Use `_ = ∫ s in A, ∫ y, c j y * conj (f j y s) ∂m ∂ν := integral_integral_swap hkA`.
-/
theorem weakae : WeakAE := by
  intro Y S ι _ _ _ m _ ν _ F f c q hf hc hint hq hw
  classical
  have hki : ∀ j, Integrable (fun p : Y × S => c j p.1 * conj (f j p.1 p.2)) (m.prod ν) := fun j =>
    integrable_k m ν (F j) (f j) (c j) (hf j) (hc j) (hint j)
  have hGj : ∀ j, Integrable (fun s => ∫ y, c j y * conj (f j y s) ∂m) ν := fun j =>
    (hki j).integral_prod_right
  have hG : Integrable (fun s => ∑ j, ∫ y, c j y * conj (f j y s) ∂m) ν :=
    integrable_finsetSum _ fun j _ => hGj j
  have hq' : Integrable q ν := hq.integrable (by norm_num)
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _ hG hq' fun A hA hνA => ?_
  have hR : ∫ s, q s * (indicatorConstLp 2 hA hνA.ne (1 : ℂ)) s ∂ν = ∫ s in A, q s ∂ν := by
    rw [← integral_indicator hA]
    refine integral_congr_ae ?_
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hνA.ne) (c := (1 : ℂ))] with s hs
    rw [hs]
    by_cases h : s ∈ A <;> simp [h]
  rw [← hR, ← hw, integral_finsetSum _ fun j _ => (hGj j).integrableOn]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hres : m.prod (ν.restrict A) = (m.prod ν).restrict (Set.univ ×ˢ A) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hkA : Integrable (Function.uncurry fun y s => c j y * conj (f j y s)) (m.prod (ν.restrict A)) := by
    rw [hres]; exact (hki j).restrict
  symm
  calc ∫ y, c j y * inner ℂ (F j y) (indicatorConstLp 2 hA hνA.ne (1 : ℂ)) ∂m
      = ∫ y, ∫ s in A, c j y * conj (f j y s) ∂ν ∂m := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [inner_ind ν (F j y) (f j y) ((hf j).2 y) A hA hνA.ne, integral_const_mul]
    _ = ∫ s in A, ∫ y, c j y * conj (f j y s) ∂m ∂ν := integral_integral_swap hkA

end PositivityTheory.Rg.BcB.E2.P
