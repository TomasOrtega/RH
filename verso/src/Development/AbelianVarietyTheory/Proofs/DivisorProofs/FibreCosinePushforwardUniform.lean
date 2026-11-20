import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FsOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StereographicMeasureChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MobiusChangeOfVariablesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreCosineExplicitFormulaStatement
open MeasureTheory
open scoped ComplexOrder ENNReal

set_option autoImplicit false

namespace GlobalTheory.FibCos

/- English proof (translation)
Use `set β : ℂ := G 1 0 / G 0 0`. Use `set c : ℂ := (Real.sqrt G.det.re / (G 0 0).re : ℂ)`. Establish `hdet : 0 < G.det.re` using `(Complex.pos_iff.1 hG.det_pos).1`. Establish `ha : 0 < (G 0 0).re` using `(Complex.pos_iff.1 (hG.diag_pos (i := 0))).1`. Establish `hc : c ≠ 0`.

Simplify using `only [c]`. Conclude with `(div_pos (Real.sqrt_pos.2 hdet) ha).ne'` after adjusting the coercions. Use `set g : ℝ → ℝ≥0∞ := J.indicator (fun _ => (1 : ENNReal))`. Establish `hg : Measurable g` using `measurable_one.indicator hJ`. Use `set H : ℂ → ℝ≥0∞ := fun y => g (1 / (1 + ‖y‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖y‖ ^ 2) ^ 2))`.

Establish `hH : Measurable H`. Simplify using `only [H]`. Use `fun_prop`. Establish `hnull : volume {x : ℂ | 1 + β * x = 0} = 0`. Apply `Set.Subsingleton.measure_zero` to reduce the goal to its premises.

Introduce `u hu v hv`. Simplify using `only [Set.mem_setOf_eq] at hu hv`. Establish `hb : β ≠ 0` using `by rintro hb; simp [hb] at hu`. Establish `: β * u = β * v` using `by linear_combination hu - hv`. Conclude with `mul_left_cancel₀ hb this`.

Establish `hae : (fun x : ℂ => g (cos G x) * ENNReal.ofReal (fs G x)) =ᵐ[volume] fun x => ENNReal.ofReal (‖c / (1 + β * x) ^ 2‖ ^ 2) * H (c * x / (1 + β * x))`. Rewrite using `[Filter.EventuallyEq, ae_iff]`. Use `measure_mono_null (fun x hx => ?_) hnull` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hx ⊢`. Assume the negation of the conclusion as `hne`.

Apply `hx` to reduce the goal to its premises. Take `⟨h1, h2⟩` from `GlobalTheory.T.fibre_cosine_explicit_formula G hG x hne`. Simplify using `only [H]`. Rewrite using `[h1, h2, ENNReal.ofReal_mul (by positivity)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[lintegral_congr_ae hae, GlobalTheory.T.mobius_change_of_variables β c hc H hH, GlobalTheory.T.stereographic_measure_change g hg, lintegral_indicator_const hJ, one_mul, Measure.restrict_apply hJ]`. Conclude with `measure_congr (Filter.EventuallyEq.inter (Filter.EventuallyEq.refl _ _) Ioo_ae_eq_Icc)`.
-/
theorem lintegral_indicator_cos_mul_fs (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) (J : Set ℝ)
    (hJ : MeasurableSet J) :
    ∫⁻ x : ℂ, J.indicator (fun _ => (1 : ENNReal)) (cos G x) * ENNReal.ofReal (fs G x) =
      volume (J ∩ Set.Icc (0 : ℝ) 1) := by
  set β : ℂ := G 1 0 / G 0 0
  set c : ℂ := (Real.sqrt G.det.re / (G 0 0).re : ℂ)
  have hdet : 0 < G.det.re := (Complex.pos_iff.1 hG.det_pos).1
  have ha : 0 < (G 0 0).re := (Complex.pos_iff.1 (hG.diag_pos (i := 0))).1
  have hc : c ≠ 0 := by
    simp only [c]
    exact_mod_cast (div_pos (Real.sqrt_pos.2 hdet) ha).ne'
  set g : ℝ → ℝ≥0∞ := J.indicator (fun _ => (1 : ENNReal))
  have hg : Measurable g := measurable_one.indicator hJ
  set H : ℂ → ℝ≥0∞ := fun y => g (1 / (1 + ‖y‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖y‖ ^ 2) ^ 2))
  have hH : Measurable H := by
    simp only [H]
    fun_prop
  have hnull : volume {x : ℂ | 1 + β * x = 0} = 0 := by
    apply Set.Subsingleton.measure_zero
    intro u hu v hv
    simp only [Set.mem_setOf_eq] at hu hv
    have hb : β ≠ 0 := by rintro hb; simp [hb] at hu
    have : β * u = β * v := by linear_combination hu - hv
    exact mul_left_cancel₀ hb this
  have hae : (fun x : ℂ => g (cos G x) * ENNReal.ofReal (fs G x)) =ᵐ[volume]
      fun x => ENNReal.ofReal (‖c / (1 + β * x) ^ 2‖ ^ 2) * H (c * x / (1 + β * x)) := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) hnull
    simp only [Set.mem_setOf_eq] at hx ⊢
    by_contra hne
    apply hx
    obtain ⟨h1, h2⟩ := GlobalTheory.T.fibre_cosine_explicit_formula G hG x hne
    simp only [H]
    rw [h1, h2, ENNReal.ofReal_mul (by positivity)]
    ring
  rw [lintegral_congr_ae hae, GlobalTheory.T.mobius_change_of_variables β c hc H hH, GlobalTheory.T.stereographic_measure_change g hg,
    lintegral_indicator_const hJ, one_mul, Measure.restrict_apply hJ]
  exact measure_congr (Filter.EventuallyEq.inter (Filter.EventuallyEq.refl _ _) Ioo_ae_eq_Icc)

end GlobalTheory.FibCos
