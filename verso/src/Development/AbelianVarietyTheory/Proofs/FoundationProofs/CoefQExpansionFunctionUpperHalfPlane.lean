import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Take `⟨C, A, hC⟩` from `ha`. Break down `eq_or_ne q 0 with rfl | hq0` into its components or cases. Conclude with `(hasSum_single 0 (fun n hn => by simp [zero_pow hn])).summable`. Establish `hr0 : 0 < ‖q‖` using `norm_pos_iff.2 hq0`. Establish `hr : ‖‖q‖‖ < 1` using `by rwa [norm_norm]`.

Establish `h` using `(summable_nat_add_iff 1).mpr (summable_pow_mul_geometric_of_norm_lt_one A hr : Summable fun m : ℕ => (m : ℝ) ^ A * ‖q‖ ^ m)`. Use `Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (h.mul_left (C * ‖q‖⁻¹))` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`. Establish `hq' : ‖q‖ ≠ 0` using `hr0.ne'`. Establish `e : C * ‖q‖⁻¹ * (((n + 1 : ℕ) : ℝ) ^ A * ‖q‖ ^ (n + 1)) = C * ((n : ℝ) + 1) ^ A * ‖q‖ ^ n`.

Use `push_cast`. Rewrite using `[pow_succ]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `mul_le_mul_of_nonneg_right (hC n) (by positivity)`.
-/
theorem summable_norm_mul_pow_of_polyB {a : ℕ → ℂ} (ha : PolyB a) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖a n * q ^ n‖ := by
  obtain ⟨C, A, hC⟩ := ha
  rcases eq_or_ne q 0 with rfl | hq0
  · exact (hasSum_single 0 (fun n hn => by simp [zero_pow hn])).summable
  · have hr0 : 0 < ‖q‖ := norm_pos_iff.2 hq0
    have hr : ‖‖q‖‖ < 1 := by rwa [norm_norm]
    have h := (summable_nat_add_iff 1).mpr
      (summable_pow_mul_geometric_of_norm_lt_one A hr : Summable fun m : ℕ => (m : ℝ) ^ A * ‖q‖ ^ m)
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (h.mul_left (C * ‖q‖⁻¹))
    rw [norm_mul, norm_pow]
    have hq' : ‖q‖ ≠ 0 := hr0.ne'
    have e : C * ‖q‖⁻¹ * (((n + 1 : ℕ) : ℝ) ^ A * ‖q‖ ^ (n + 1)) = C * ((n : ℝ) + 1) ^ A * ‖q‖ ^ n := by
      push_cast
      rw [pow_succ]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (hC n) (by positivity)

/- English proof (translation)
Simplify using `only [smul_eq_mul, Function.Periodic.qParam]`. Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qs_term_eq (a : ℕ → ℂ) (τ : ℍ) (n : ℕ) :
    a n * cexp (2 * π * Complex.I * n * τ) = a n • (Function.Periodic.qParam 1 (τ : ℂ)) ^ n := by
  simp only [smul_eq_mul, Function.Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/- English proof (translation)
Establish `hq : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1` using `Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos`. Establish `hs : Summable fun n => a n • Function.Periodic.qParam 1 (τ : ℂ) ^ n`. Simplify `(summable_norm_mul_pow_of_polyB ha hq).of_norm` using `only [smul_eq_mul]`. Use `hs.hasSum using 1` and compare the differences between its conclusion and the goal. Use `show ∑' n, a n * cexp (2 * π * Complex.I * n * τ) = _`.

Conclude with `tsum_congr fun n => qs_term_eq a τ n`.
-/
theorem hasSum_qs {a : ℕ → ℂ} (ha : PolyB a) (τ : ℍ) :
    HasSum (fun n : ℕ => a n • (Function.Periodic.qParam 1 (τ : ℂ)) ^ n) (qs a τ) := by
  have hq : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hs : Summable fun n => a n • Function.Periodic.qParam 1 (τ : ℂ) ^ n := by
    simpa only [smul_eq_mul] using (summable_norm_mul_pow_of_polyB ha hq).of_norm
  convert hs.hasSum using 1
  show ∑' n, a n * cexp (2 * π * Complex.I * n * τ) = _
  exact tsum_congr fun n => qs_term_eq a τ n

/- English proof (translation)
Rewrite using `[UpperHalfPlane.mdifferentiable_iff]`. Introduce `z hz`. Establish `hz' : 0 < z.im` using `hz`. Use `set y0 := z.im / 2 with hy0def`. Establish `hy0 : 0 < y0` using `by positivity`.

Use `set U : Set ℂ := {w | y0 < w.im} with hUdef`. Establish `hU : IsOpen U` using `isOpen_lt continuous_const Complex.continuous_im`. Establish `hzU : z ∈ U` using `by show y0 < z.im`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set r : ℝ := Real.exp (-(2 * π * y0)) with hrdef`.

Establish `hr0 : 0 < r` using `Real.exp_pos _`. Establish `hr1 : ‖(r : ℂ)‖ < 1`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hrdef, Real.exp_lt_one_iff]`. Use `Real.pi_pos` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `hD : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * w)) U`. Use `Complex.differentiableOn_tsum_of_summable_norm (summable_norm_mul_pow_of_polyB ha hr1) (fun n => (by fun_prop : Differentiable ℂ fun w : ℂ => a n * cexp (2 * π * Complex.I * n * w)).differentiableOn) hU ?_` and prove the remaining obligations. Introduce `n w hw`. Rewrite using `[norm_mul, norm_mul, Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hrdef, ← Real.exp_nat_mul]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations.

Rewrite using `[Real.exp_le_exp]`. Establish `hre : (2 * π * Complex.I * n * w).re = -(2 * π * n * w.im)`. Simplify using `[Complex.mul_re, Complex.mul_im]`. Rewrite using `[hre]`. Establish `hn : (0 : ℝ) ≤ n` using `n.cast_nonneg`.

Establish `hw' : y0 < w.im` using `hw`. Use `mul_nonneg (mul_nonneg Real.pi_pos.le hn) (sub_pos.2 hw').le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hDz` using `(hD z hzU).differentiableAt (hU.mem_nhds hzU)`. Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises.

Apply `hDz.congr_of_eventuallyEq` to reduce the goal to its premises. Use `filter_upwards [hU.mem_nhds hzU] with w hw`. Establish `hw' : 0 < w.im` using `lt_trans hy0 hw`. Rewrite using `[Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw']`. Both sides reduce to the same expression.
-/
private theorem mdifferentiable_qs_of_polyB {a : ℕ → ℂ} (ha : PolyB a) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qs a) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have hz' : 0 < z.im := hz
  set y0 := z.im / 2 with hy0def
  have hy0 : 0 < y0 := by positivity
  set U : Set ℂ := {w | y0 < w.im} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hzU : z ∈ U := by
    show y0 < z.im
    linarith
  set r : ℝ := Real.exp (-(2 * π * y0)) with hrdef
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : ‖(r : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hrdef, Real.exp_lt_one_iff]
    have := Real.pi_pos
    nlinarith
  have hD : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * w)) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm (summable_norm_mul_pow_of_polyB ha hr1)
      (fun n => (by fun_prop : Differentiable ℂ fun w : ℂ => a n * cexp (2 * π * Complex.I * n * w)).differentiableOn)
      hU ?_
    intro n w hw
    rw [norm_mul, norm_mul, Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0, hrdef, ← Real.exp_nat_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Real.exp_le_exp]
    have hre : (2 * π * Complex.I * n * w).re = -(2 * π * n * w.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have hw' : y0 < w.im := hw
    have := mul_nonneg (mul_nonneg Real.pi_pos.le hn) (sub_pos.2 hw').le
    nlinarith
  have hDz := (hD z hzU).differentiableAt (hU.mem_nhds hzU)
  apply DifferentiableAt.differentiableWithinAt
  apply hDz.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hzU] with w hw
  have hw' : 0 < w.im := lt_trans hy0 hw
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw']
  rfl

/- English proof (translation)
Introduce `w`. Distinguish the cases in `hw : 0 < w.im`. Establish `hw1 : 0 < (w + 1).im` using `by simpa using hw`. Simplify using `only [Function.comp_apply, ofComplex_apply_of_im_pos hw1, ofComplex_apply_of_im_pos hw]`. Use `show ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * (w + 1)) = ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * w)`.

Use `tsum_congr fun n => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[show 2 * π * Complex.I * n * (w + 1) = 2 * π * Complex.I * n * w + n * (2 * π * Complex.I) by ring, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]`. Use `push_neg at hw`. Establish `hw1 : (w + 1).im ≤ 0` using `by simpa using hw`.

Simplify using `only [Function.comp_apply, ofComplex_apply_of_im_nonpos hw1, ofComplex_apply_of_im_nonpos hw]`.
-/
private theorem periodic_qs_comp_ofComplex_one (a : ℕ → ℂ) :
    Function.Periodic (qs a ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < w.im
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw1, ofComplex_apply_of_im_pos hw]
    show ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * (w + 1))
      = ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * w)
    refine tsum_congr fun n => ?_
    congr 1
    rw [show 2 * π * Complex.I * n * (w + 1) = 2 * π * Complex.I * n * w + n * (2 * π * Complex.I) by ring,
      Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  · push_neg at hw
    have hw1 : (w + 1).im ≤ 0 := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos hw1, ofComplex_apply_of_im_nonpos hw]

/- English proof (translation)
Conclude with `analyticAt_cuspFunction_zero one_pos (periodic_qs_comp_ofComplex_one a) (mdifferentiable_qs_of_polyB ha) (isBoundedAtImInfty_of_hasSum_qExpansion one_pos (hasSum_qs ha))`.
-/
theorem analyticAt_cuspFunction_qs {a : ℕ → ℂ} (ha : PolyB a) :
    AnalyticAt ℂ (cuspFunction 1 (qs a)) 0 := by
  exact analyticAt_cuspFunction_zero one_pos (periodic_qs_comp_ofComplex_one a)
    (mdifferentiable_qs_of_polyB ha) (isBoundedAtImInfty_of_hasSum_qExpansion one_pos (hasSum_qs ha))

/- English proof (translation)
Introduce `a ha n`. Establish `hb` using `analyticAt_cuspFunction_qs ha`. Establish `h1` using `(hasFPowerSeriesOnBall_cuspFunction one_pos hb (hasSum_qs ha)).hasFPowerSeriesAt`. Establish `h2` using `hb.hasFPowerSeriesAt`. Establish `e` using `congr_arg (FormalMultilinearSeries.coeff · n) (h1.eq_formalMultilinearSeries h2)`.

Simplify using `only [FormalMultilinearSeries.coeff_ofScalars] at e`. Use `show (qExpansion 1 (qs a)).coeff n = a n`. Rewrite using `[qExpansion_coeff, e, div_eq_inv_mul]`.
-/
theorem coef_qs : ∀ a : ℕ → ℂ, PolyB a → ∀ n, coef (qs a) n = a n := by
  intro a ha n
  have hb := analyticAt_cuspFunction_qs ha
  have h1 := (hasFPowerSeriesOnBall_cuspFunction one_pos hb (hasSum_qs ha)).hasFPowerSeriesAt
  have h2 := hb.hasFPowerSeriesAt
  have e := congr_arg (FormalMultilinearSeries.coeff · n) (h1.eq_formalMultilinearSeries h2)
  simp only [FormalMultilinearSeries.coeff_ofScalars] at e
  show (qExpansion 1 (qs a)).coeff n = a n
  rw [qExpansion_coeff, e, div_eq_inv_mul]

end GlobalTheory.EisM
