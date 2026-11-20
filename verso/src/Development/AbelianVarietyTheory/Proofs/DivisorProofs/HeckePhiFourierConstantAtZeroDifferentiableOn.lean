import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwoC

open MeasureTheory

def lg (t : ℝ) : ℝ := Real.log ‖(t : ℂ) + I‖

/- English proof (translation)
Introduce `h`. Use `congrArg Complex.im h` as an intermediate fact. Simplify using `at this`.
-/
theorem tI_ne (t : ℝ) : (t : ℂ) + I ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this

/- English proof (translation)
Rewrite using `[Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, sq_abs]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sq_norm_tI (t : ℝ) : ‖(t : ℂ) + I‖ ^ 2 = 1 + ‖t‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, sq_abs]; simp; ring

/- English proof (translation)
The claim follows from `(Real.exp_log (norm_pos_iff.2 (tI_ne t))).symm`.
-/
theorem norm_tI_eq (t : ℝ) : ‖(t : ℂ) + I‖ = Real.exp (lg t) :=
  (Real.exp_log (norm_pos_iff.2 (tI_ne t))).symm

/- English proof (translation)
Apply `Real.log_nonneg` to reduce the goal to its premises. Establish `h` using `sq_norm_tI t`. Use polynomial arithmetic with `[norm_nonneg ((t : ℂ) + I), sq_nonneg ‖t‖]`.
-/
theorem lg_nonneg (t : ℝ) : 0 ≤ lg t := by
  apply Real.log_nonneg
  have h := sq_norm_tI t
  nlinarith [norm_nonneg ((t : ℂ) + I), sq_nonneg ‖t‖]

/- English proof (translation)
Unfold `lg`. Conclude with `(Continuous.norm (by fun_prop)).log (fun t => (norm_pos_iff.2 (tI_ne t)).ne')`.
-/
theorem continuous_lg : Continuous lg := by
  unfold lg
  exact (Continuous.norm (by fun_prop)).log (fun t => (norm_pos_iff.2 (tI_ne t)).ne')

def G (σ : ℂ) (t : ℝ) : ℂ := ((t : ℂ) + I)⁻¹ ^ 2 * Complex.exp ((lg t : ℂ) * (-2 * σ))

def G' (σ : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) + I)⁻¹ ^ 2 * (Complex.exp ((lg t : ℂ) * (-2 * σ)) * ((lg t : ℂ) * (-2)))

/- English proof (translation)
Use function extensionality and compare the values at `σ`. Unfold `cConst hTrans G`. Use `congr 1`. Use function extensionality and compare the values at `t`. Simplify using `only [ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one, ofReal_one, one_mul]`.

Unfold `phi`. Use `congr 1`. Rewrite using `[Complex.cpow_def_of_ne_zero (by exact_mod_cast (norm_pos_iff.2 (tI_ne t)).ne'), ← Complex.ofReal_log (norm_nonneg _)]`. Both sides reduce to the same expression.
-/
theorem cConst_eq : cConst = fun σ => ∫ t, G σ t := by
  funext σ
  unfold cConst hTrans G
  congr 1; funext t
  simp only [ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one, ofReal_one, one_mul]
  unfold phi
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (norm_pos_iff.2 (tI_ne t)).ne'),
    ← Complex.ofReal_log (norm_nonneg _)]
  rfl

/- English proof (translation)
Unfold `G`. Rewrite using `[norm_mul, norm_pow, norm_inv, norm_tI_eq, Complex.norm_exp, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add]`. Use `congr 1`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_G (σ : ℂ) (t : ℝ) : ‖G σ t‖ = Real.exp (-(2 + 2 * σ.re) * lg t) := by
  unfold G
  rw [norm_mul, norm_pow, norm_inv, norm_tI_eq, Complex.norm_exp, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  simp
  ring

/- English proof (translation)
Establish `: G' σ t = G σ t * ((lg t : ℂ) * (-2))` using `by unfold G G'; ring`. Rewrite using `[this, norm_mul, norm_G, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lg_nonneg t)]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_G' (σ : ℂ) (t : ℝ) : ‖G' σ t‖ = Real.exp (-(2 + 2 * σ.re) * lg t) * (2 * lg t) := by
  have : G' σ t = G σ t * ((lg t : ℂ) * (-2)) := by unfold G G'; ring
  rw [this, norm_mul, norm_G, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lg_nonneg t)]
  simp; ring

/- English proof (translation)
Rewrite using `[norm_G]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Use `lg_nonneg t` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem bound_G {ε : ℝ} (hε : 0 < ε) {σ : ℂ} (hσ : -1 / 2 + ε ≤ σ.re) (t : ℝ) :
    ‖G σ t‖ ≤ Real.exp (-(1 + ε) * lg t) := by
  rw [norm_G]
  apply Real.exp_le_exp.2
  have := lg_nonneg t
  nlinarith

/- English proof (translation)
Rewrite using `[norm_G']`. Establish `hL` using `lg_nonneg t`. Establish `h1 : Real.exp (-(2 + 2 * σ.re) * lg t) ≤ Real.exp (-(1 + ε) * lg t) * Real.exp (-(ε * lg t))`. Rewrite using `[← Real.exp_add]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : ε * lg t + 1 ≤ Real.exp (ε * lg t)` using `Real.add_one_le_exp _`. Establish `h3 : Real.exp (-(ε * lg t)) * (2 * lg t) ≤ 2 / ε`. Rewrite using `[Real.exp_neg, le_div_iff₀ hε]`. Establish `hp` using `Real.exp_pos (ε * lg t)`.

Rewrite using `[show (Real.exp (ε * lg t))⁻¹ * (2 * lg t) * ε = 2 * (ε * lg t) / Real.exp (ε * lg t) by field_simp]`. Rewrite using `[div_le_iff₀ hp]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem bound_G' {ε : ℝ} (hε : 0 < ε) {σ : ℂ} (hσ : -1 / 2 + ε ≤ σ.re) (t : ℝ) :
    ‖G' σ t‖ ≤ 2 / ε * Real.exp (-(1 + ε) * lg t) := by
  rw [norm_G']
  have hL := lg_nonneg t
  have h1 : Real.exp (-(2 + 2 * σ.re) * lg t) ≤ Real.exp (-(1 + ε) * lg t) * Real.exp (-(ε * lg t)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  have h2 : ε * lg t + 1 ≤ Real.exp (ε * lg t) := Real.add_one_le_exp _
  have h3 : Real.exp (-(ε * lg t)) * (2 * lg t) ≤ 2 / ε := by
    rw [Real.exp_neg, le_div_iff₀ hε]
    have hp := Real.exp_pos (ε * lg t)
    rw [show (Real.exp (ε * lg t))⁻¹ * (2 * lg t) * ε = 2 * (ε * lg t) / Real.exp (ε * lg t) by field_simp]
    rw [div_le_iff₀ hp]
    linarith
  calc Real.exp (-(2 + 2 * σ.re) * lg t) * (2 * lg t)
      ≤ Real.exp (-(1 + ε) * lg t) * Real.exp (-(ε * lg t)) * (2 * lg t) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
    _ = Real.exp (-(1 + ε) * lg t) * (Real.exp (-(ε * lg t)) * (2 * lg t)) := by ring
    _ ≤ Real.exp (-(1 + ε) * lg t) * (2 / ε) := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = 2 / ε * Real.exp (-(1 + ε) * lg t) := by ring

/- English proof (translation)
Establish `h` using `integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 1 + ε) (by simp; linarith)`. Use `h.congr (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← sq_norm_tI, norm_tI_eq, ← Real.exp_nat_mul, ← Real.exp_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integrable_expL {ε : ℝ} (hε : 0 < ε) : Integrable (fun t : ℝ => Real.exp (-(1 + ε) * lg t)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 1 + ε) (by simp; linarith)
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [← sq_norm_tI, norm_tI_eq, ← Real.exp_nat_mul, ← Real.exp_mul]
  congr 1; push_cast; ring

/- English proof (translation)
Unfold `G G'`. Establish `h : HasDerivAt (fun s : ℂ => (lg t : ℂ) * (-2 * s)) ((lg t : ℂ) * (-2)) σ`. Conclude with `(((hasDerivAt_id σ).const_mul (-2 : ℂ)).const_mul (lg t : ℂ)).congr_deriv (by ring)`. Conclude with `h.cexp.const_mul _`.
-/
theorem hasDerivAt_G (σ : ℂ) (t : ℝ) : HasDerivAt (fun s => G s t) (G' σ t) σ := by
  unfold G G'
  have h : HasDerivAt (fun s : ℂ => (lg t : ℂ) * (-2 * s)) ((lg t : ℂ) * (-2)) σ := by
    exact (((hasDerivAt_id σ).const_mul (-2 : ℂ)).const_mul (lg t : ℂ)).congr_deriv (by ring)
  exact h.cexp.const_mul _

/- English proof (translation)
Unfold `G`. Establish `: Continuous fun t : ℝ => ((t : ℂ) + I)⁻¹` using `(by fun_prop : Continuous fun t : ℝ => (t : ℂ) + I).inv₀ tI_ne`. Conclude with `(this.pow 2).mul (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_lg).mul continuous_const))`.
-/
theorem continuous_G (σ : ℂ) : Continuous (G σ) := by
  unfold G
  have : Continuous fun t : ℝ => ((t : ℂ) + I)⁻¹ :=
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ) + I).inv₀ tI_ne
  exact (this.pow 2).mul (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp continuous_lg).mul continuous_const))

/- English proof (translation)
Establish `: G' σ = fun t => G σ t * ((lg t : ℂ) * (-2))` using `by funext t; unfold G G'; ring`. Rewrite using `[this]`. Conclude with `(continuous_G σ).mul ((Complex.continuous_ofReal.comp continuous_lg).mul continuous_const)`.
-/
theorem continuous_G' (σ : ℂ) : Continuous (G' σ) := by
  have : G' σ = fun t => G σ t * ((lg t : ℂ) * (-2)) := by funext t; unfold G G'; ring
  rw [this]
  exact (continuous_G σ).mul ((Complex.continuous_ofReal.comp continuous_lg).mul continuous_const)

end GlobalTheory.HeckeTwoC

namespace GlobalTheory.HeckeTwo

open MeasureTheory GlobalTheory.HeckeTwoC

/- English proof (translation)
Rewrite using `[cConst_eq]`. Introduce `σ₀ hσ₀`. Establish `hre : -1 / 2 < σ₀.re` using `hσ₀`. Use `set ε := (σ₀.re + 1 / 2) / 2 with hε_def`. Establish `hε : 0 < ε` using `by rw [hε_def]; linarith`.

Establish `hball : ∀ σ ∈ Metric.ball σ₀ ε, -1 / 2 + ε ≤ σ.re`. Introduce `σ hσ`. Establish `h1 : |(σ - σ₀).re| ≤ ‖σ - σ₀‖` using `Complex.abs_re_le_norm _`. Establish `h2 : ‖σ - σ₀‖ < ε` using `by simpa [dist_eq_norm] using hσ`. Establish `h3` using `(abs_lt.1 (lt_of_le_of_lt h1 h2)).1`.

Simplify using `only [sub_re] at h3`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := G) (F' := G') (x₀ := σ₀) (bound := fun t => 2 / ε * Real.exp (-(1 + ε) * lg t)) (Metric.ball_mem_nhds σ₀ hε) (Filter.Eventually.of_forall fun σ => (continuous_G σ).aestronglyMeasurable) ((integrable_expL hε).mon …`. Conclude with `key.2.differentiableAt.differentiableWithinAt`.
-/
theorem cConst_differentiableOn : DifferentiableOn ℂ cConst halfPlane := by
  rw [cConst_eq]
  intro σ₀ hσ₀
  have hre : -1 / 2 < σ₀.re := hσ₀
  set ε := (σ₀.re + 1 / 2) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hball : ∀ σ ∈ Metric.ball σ₀ ε, -1 / 2 + ε ≤ σ.re := by
    intro σ hσ
    have h1 : |(σ - σ₀).re| ≤ ‖σ - σ₀‖ := Complex.abs_re_le_norm _
    have h2 : ‖σ - σ₀‖ < ε := by simpa [dist_eq_norm] using hσ
    have h3 := (abs_lt.1 (lt_of_le_of_lt h1 h2)).1
    simp only [sub_re] at h3
    linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := G) (F' := G')
    (x₀ := σ₀) (bound := fun t => 2 / ε * Real.exp (-(1 + ε) * lg t))
    (Metric.ball_mem_nhds σ₀ hε)
    (Filter.Eventually.of_forall fun σ => (continuous_G σ).aestronglyMeasurable)
    ((integrable_expL hε).mono' (continuous_G σ₀).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => bound_G hε (hball σ₀ (Metric.mem_ball_self hε)) t))
    (continuous_G' σ₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t σ hσ => bound_G' hε (hball σ hσ) t)
    ((integrable_expL hε).const_mul _)
    (Filter.Eventually.of_forall fun t σ _ => hasDerivAt_G σ t)
  exact key.2.differentiableAt.differentiableWithinAt

end GlobalTheory.HeckeTwo
