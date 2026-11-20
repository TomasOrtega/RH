import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory.RealPeriodCocycle

/- English proof (translation)
Establish `hπ : 3 < π` using `Real.pi_gt_three`. Establish `hn : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `hne : ‖Complex.exp w‖ = Real.exp w.re` using `Complex.norm_exp w`. Distinguish the cases in `h1 : 1 ≤ w.re`. Establish `h2` using `norm_sub_norm_le (Complex.exp w) 1`.

Establish `h3` using `Real.add_one_le_exp w.re`. Rewrite `h2` using `[hne, norm_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `h2 : w.re ≤ -1`. Establish `h3` using `norm_sub_norm_le 1 (Complex.exp w)`.

Rewrite `h3` using `[hne, norm_one, norm_sub_rev]`. Establish `h4 : Real.exp w.re ≤ Real.exp (-1)` using `Real.exp_le_exp.2 h2`. Establish `h5 : Real.exp (-1) ≤ 1 / 2`. Use `Real.exp_neg_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Use `push Not at h1 h2`. Use `set ρ : ℝ := (2 * n + 1) * π with hρ`. Establish `hρ1 : 1 ≤ ρ` using `by nlinarith`. Establish `hsq : w.re ^ 2 + w.im ^ 2 = ρ ^ 2`.

Rewrite using `[← hw, Complex.sq_norm, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hre : w.re ^ 2 ≤ 1` using `by nlinarith`. Establish `hup : |w.im| ≤ ρ` using `hw ▸ Complex.abs_im_le_norm w`. Establish `hlo : ρ - 1 ≤ |w.im|`.

Apply `abs_le_of_sq_le_sq' _ (abs_nonneg _) |>.2` to reduce the goal to its premises. Rewrite using `[sq_abs]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hcos : Real.cos w.im ≤ 0`. Establish `e : Real.cos w.im = - Real.cos (ρ - |w.im|)`.

Rewrite using `[← Real.cos_abs w.im]`. Establish `: |w.im| = (π - (ρ - |w.im|)) + n * (2 * π)` using `by rw [hρ]; ring`. Use `conv_lhs => rw [this]`. Rewrite using `[Real.cos_add_nat_mul_two_pi, Real.cos_pi_sub]`. Rewrite using `[e, neg_nonpos]`.

Apply `Real.cos_nonneg_of_mem_Icc` to reduce the goal to its premises. Apply the tactic sequence `constructor <;> linarith`. Establish `h3` using `Complex.abs_re_le_norm (Complex.exp w - 1)`. Rewrite `h3` using `[Complex.sub_re, Complex.exp_re, Complex.one_re]`. Establish `h4 : Real.exp w.re * Real.cos w.im ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hcos`.

Establish `h5` using `neg_abs_le (Real.exp w.re * Real.cos w.im - 1)`. Establish `h6` using `neg_le_abs (Real.exp w.re * Real.cos w.im - 1)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem half_le_norm_exp_sub_one (n : ℕ) {w : ℂ} (hw : ‖w‖ = (2 * n + 1) * π) :
    1 / 2 ≤ ‖Complex.exp w - 1‖ := by
  have hπ : 3 < π := Real.pi_gt_three
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hne : ‖Complex.exp w‖ = Real.exp w.re := Complex.norm_exp w
  by_cases h1 : 1 ≤ w.re
  · have h2 := norm_sub_norm_le (Complex.exp w) 1
    have h3 := Real.add_one_le_exp w.re
    rw [hne, norm_one] at h2
    linarith
  by_cases h2 : w.re ≤ -1
  · have h3 := norm_sub_norm_le 1 (Complex.exp w)
    rw [hne, norm_one, norm_sub_rev] at h3
    have h4 : Real.exp w.re ≤ Real.exp (-1) := Real.exp_le_exp.2 h2
    have h5 : Real.exp (-1) ≤ 1 / 2 := by
      have := Real.exp_neg_one_lt_d9
      linarith
    linarith
  push Not at h1 h2
  set ρ : ℝ := (2 * n + 1) * π with hρ
  have hρ1 : 1 ≤ ρ := by nlinarith
  have hsq : w.re ^ 2 + w.im ^ 2 = ρ ^ 2 := by
    rw [← hw, Complex.sq_norm, Complex.normSq_apply]; ring
  have hre : w.re ^ 2 ≤ 1 := by nlinarith
  have hup : |w.im| ≤ ρ := hw ▸ Complex.abs_im_le_norm w
  have hlo : ρ - 1 ≤ |w.im| := by
    apply abs_le_of_sq_le_sq' _ (abs_nonneg _) |>.2
    rw [sq_abs]
    nlinarith
  have hcos : Real.cos w.im ≤ 0 := by
    have e : Real.cos w.im = - Real.cos (ρ - |w.im|) := by
      rw [← Real.cos_abs w.im]
      have : |w.im| = (π - (ρ - |w.im|)) + n * (2 * π) := by rw [hρ]; ring
      conv_lhs => rw [this]
      rw [Real.cos_add_nat_mul_two_pi, Real.cos_pi_sub]
    rw [e, neg_nonpos]
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith
  have h3 := Complex.abs_re_le_norm (Complex.exp w - 1)
  rw [Complex.sub_re, Complex.exp_re, Complex.one_re] at h3
  have h4 : Real.exp w.re * Real.cos w.im ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hcos
  have h5 := neg_abs_le (Real.exp w.re * Real.cos w.im - 1)
  have h6 := neg_le_abs (Real.exp w.re * Real.cos w.im - 1)
  linarith

noncomputable def hurwitz (n : ℕ) (z : ℂ) : ℂ :=
  (2 * π * Complex.I)⁻¹ * ∮ w in C(0, (2 * n + 1) * π),
    (1 / (w - 0) ^ (n + 1)) • (Complex.exp (w * z) / (Complex.exp w - 1))

/- English proof (translation)
Check the signs of the components of the expression.
-/
theorem radius_pos (n : ℕ) : (0 : ℝ) < (2 * n + 1) * π := by positivity

/- English proof (translation)
Introduce `h`. Use `half_le_norm_exp_sub_one n (w := w) (by simpa using hw)` as an intermediate fact. Rewrite `this` using `[h, norm_zero]`. Evaluate the numerical expressions using `at this`.
-/
theorem exp_sub_one_ne (n : ℕ) {w : ℂ} (hw : w ∈ Metric.sphere (0 : ℂ) ((2 * n + 1) * π)) :
    Complex.exp w - 1 ≠ 0 := by
  intro h
  have := half_le_norm_exp_sub_one n (w := w) (by simpa using hw)
  rw [h, norm_zero] at this
  norm_num at this

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[sub_zero]`. Use `radius_pos n` as an intermediate fact. Rewrite `hw` using `[h]`. Simplify using `only [mem_sphere_iff_norm, sub_self, norm_zero] at hw`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ne_zero_of_mem (n : ℕ) {w : ℂ} (hw : w ∈ Metric.sphere (0 : ℂ) ((2 * n + 1) * π)) :
    w - 0 ≠ 0 := by
  intro h
  rw [sub_zero] at h
  have := radius_pos n
  rw [h] at hw
  simp only [mem_sphere_iff_norm, sub_self, norm_zero] at hw
  linarith

/- English proof (translation)
Unfold `hurwitz`. Use `Differentiable.const_mul ?_ _` and prove the remaining obligations. Rewrite using `[← differentiableOn_univ]`. Unfold `circleIntegral`. Establish `hm : ∀ t, circleMap 0 ((2 * n + 1) * π) t ∈ Metric.sphere (0 : ℂ) ((2 * n + 1) * π)` using `fun t => circleMap_mem_sphere _ (radius_pos n).le t`.

Use `(GlobalTheory.differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn (F := fun (t : ℝ) (z : ℂ) => deriv (circleMap 0 ((2 * n + 1) * π)) t • ((1 / (circleMap 0 ((2 * n + 1) * π) t - 0) ^ (n + 1)) • (Complex.exp (circleMap 0 ((2 * n + 1) * π) t * z) / (Complex.exp (circle …` and prove the remaining obligations. Apply `Continuous.continuousOn` to reduce the goal to its premises. Simplify using `only [deriv_circleMap, smul_eq_mul]`. Unfold `Function.uncurry`. Establish `hc : Continuous fun p : ℝ × ℂ => circleMap 0 ((2 * n + 1) * π) p.1` using `(continuous_circleMap _ _).comp continuous_fst`.

Use `(hc.mul continuous_const).mul (Continuous.mul ?_ ?_)` and prove the remaining obligations. Conclude with `continuous_const.div ((hc.sub continuous_const).pow _) fun p => pow_ne_zero _ (ne_zero_of_mem n (hm _))`. Conclude with `(Complex.continuous_exp.comp (hc.mul continuous_snd)).div ((Complex.continuous_exp.comp hc).sub continuous_const) fun p => exp_sub_one_ne n (hm _)`. Introduce `t _`. Apply `Differentiable.differentiableOn` to reduce the goal to its premises.

Simplify using `only [smul_eq_mul]`. Use `fun_prop`.
-/
theorem differentiable_hurwitz (n : ℕ) : Differentiable ℂ (hurwitz n) := by
  unfold hurwitz
  refine Differentiable.const_mul ?_ _
  rw [← differentiableOn_univ]
  unfold circleIntegral
  have hm : ∀ t, circleMap 0 ((2 * n + 1) * π) t ∈ Metric.sphere (0 : ℂ) ((2 * n + 1) * π) :=
    fun t => circleMap_mem_sphere _ (radius_pos n).le t
  refine (GlobalTheory.differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
    (F := fun (t : ℝ) (z : ℂ) => deriv (circleMap 0 ((2 * n + 1) * π)) t •
      ((1 / (circleMap 0 ((2 * n + 1) * π) t - 0) ^ (n + 1)) •
        (Complex.exp (circleMap 0 ((2 * n + 1) * π) t * z) /
          (Complex.exp (circleMap 0 ((2 * n + 1) * π) t) - 1)))) isOpen_univ ?_ ?_).1
  · apply Continuous.continuousOn
    simp only [deriv_circleMap, smul_eq_mul]
    unfold Function.uncurry
    have hc : Continuous fun p : ℝ × ℂ => circleMap 0 ((2 * n + 1) * π) p.1 :=
      (continuous_circleMap _ _).comp continuous_fst
    refine (hc.mul continuous_const).mul (Continuous.mul ?_ ?_)
    · exact continuous_const.div ((hc.sub continuous_const).pow _)
        fun p => pow_ne_zero _ (ne_zero_of_mem n (hm _))
    · exact (Complex.continuous_exp.comp (hc.mul continuous_snd)).div
        ((Complex.continuous_exp.comp hc).sub continuous_const) fun p => exp_sub_one_ne n (hm _)
  · intro t _
    apply Differentiable.differentiableOn
    simp only [smul_eq_mul]
    fun_prop

/- English proof (translation)
Apply `ContinuousOn.circleIntegrable (radius_pos n).le` to reduce the goal to its premises. Simplify using `only [smul_eq_mul]`. Use `ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun w hw => pow_ne_zero _ (ne_zero_of_mem n hw)) (ContinuousOn.div (by fun_prop) (by fun_prop) fun w hw => exp_sub_one_ne n hw)` and prove the remaining obligations.
-/
theorem circleIntegrable_kernel (n : ℕ) (z : ℂ) : CircleIntegrable (fun w : ℂ =>
    (1 / (w - 0) ^ (n + 1)) • (Complex.exp (w * z) / (Complex.exp w - 1))) 0
      ((2 * n + 1) * π) := by
  apply ContinuousOn.circleIntegrable (radius_pos n).le
  simp only [smul_eq_mul]
  refine ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop)
    fun w hw => pow_ne_zero _ (ne_zero_of_mem n hw)) (ContinuousOn.div (by fun_prop) (by fun_prop)
    fun w hw => exp_sub_one_ne n hw)

/- English proof (translation)
Establish `h1` using `(show DifferentiableOn ℂ (fun w : ℂ => Complex.exp (w * z)) (Metric.closedBall 0 ((2 * n + 1) * π)) by fun_prop).circleIntegral_one_div_sub_center_pow_smul (radius_pos n) n`. Establish `h2 : iteratedDeriv n (fun w : ℂ => Complex.exp (w * z)) 0 = z ^ n`. Use `congrFun (iteratedDeriv_cexp_const_mul n z) 0` as an intermediate fact. Simplify using `only [mul_comm z] at this`. Simplify using `using this`.

Rewrite `h1` using `[h2]`. Establish `h3` using `circleIntegral.integral_sub (circleIntegrable_kernel n (z + 1)) (circleIntegrable_kernel n z)`. Establish `h4 : (∮ w in C(0, (2 * n + 1) * π), ((1 / (w - 0) ^ (n + 1)) • (Complex.exp (w * (z + 1)) / (Complex.exp w - 1)) - (1 / (w - 0) ^ (n + 1)) • (Complex.exp (w * z) / (Complex.exp w - 1)))) = ∮ w in C(0, (2 * n + 1) * π), (1 / (w - 0) ^ (n + 1)) • Complex.exp (w * z)`. Apply `circleIntegral.integral_congr (radius_pos n).le` to reduce the goal to its premises. Introduce `w hw`.

Use `exp_sub_one_ne n hw` as an intermediate fact. Simplify using `only [smul_eq_mul, mul_add, mul_one, Complex.exp_add]`. Clear the denominators using the available nonvanishing facts. Rewrite `h3` using `[h4, h1]`. Unfold `hurwitz`.

Rewrite using `[← sub_eq_iff_eq_add', ← mul_sub, ← h3, smul_eq_mul]`. Establish `: (π : ℂ) ≠ 0` using `by simp [Real.pi_ne_zero]`. Clear the denominators using the available nonvanishing facts.
-/
theorem hurwitz_add_one (n : ℕ) (z : ℂ) :
    hurwitz n (z + 1) = hurwitz n z + (n.factorial : ℂ)⁻¹ * z ^ n := by
  have h1 := (show DifferentiableOn ℂ (fun w : ℂ => Complex.exp (w * z))
    (Metric.closedBall 0 ((2 * n + 1) * π)) by
      fun_prop).circleIntegral_one_div_sub_center_pow_smul (radius_pos n) n
  have h2 : iteratedDeriv n (fun w : ℂ => Complex.exp (w * z)) 0 = z ^ n := by
    have := congrFun (iteratedDeriv_cexp_const_mul n z) 0
    simp only [mul_comm z] at this
    simpa using this
  rw [h2] at h1
  have h3 := circleIntegral.integral_sub (circleIntegrable_kernel n (z + 1))
    (circleIntegrable_kernel n z)
  have h4 : (∮ w in C(0, (2 * n + 1) * π),
      ((1 / (w - 0) ^ (n + 1)) • (Complex.exp (w * (z + 1)) / (Complex.exp w - 1)) -
      (1 / (w - 0) ^ (n + 1)) • (Complex.exp (w * z) / (Complex.exp w - 1)))) =
      ∮ w in C(0, (2 * n + 1) * π), (1 / (w - 0) ^ (n + 1)) • Complex.exp (w * z) := by
    apply circleIntegral.integral_congr (radius_pos n).le
    intro w hw
    have := exp_sub_one_ne n hw
    simp only [smul_eq_mul, mul_add, mul_one, Complex.exp_add]
    field_simp
  rw [h4, h1] at h3
  unfold hurwitz
  rw [← sub_eq_iff_eq_add', ← mul_sub, ← h3, smul_eq_mul]
  have : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  field_simp

/- English proof (translation)
Use `set ρ : ℝ := (2 * n + 1) * π with hρ`. Establish `hρ0 : 0 < ρ` using `radius_pos n`. Establish `h1 : ‖hurwitz n z‖ ≤ ρ * (1 / ρ ^ (n + 1) * (Real.exp (ρ * S) / (1 / 2)))`. Unfold `hurwitz`. Rewrite using `[← smul_eq_mul]`.

Apply `circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρ0.le` to reduce the goal to its premises. Introduce `w hw`. Establish `hw' : ‖w‖ = ρ` using `by simpa using hw`. Rewrite using `[norm_smul, norm_div, norm_div, norm_pow, sub_zero, hw', norm_one]`. Use `mul_le_mul_of_nonneg_left ?_ (by positivity)` and prove the remaining obligations.

Use `div_le_div₀ (by positivity) ?_ (by norm_num) (half_le_norm_exp_sub_one n hw')` and prove the remaining obligations. Use `(Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, hw']`. Conclude with `mul_le_mul_of_nonneg_left hz hρ0.le`. Establish `h2 : (n.factorial : ℝ) ≤ ρ ^ n`.

Establish `a : (n.factorial : ℝ) ≤ (n : ℝ) ^ n` using `by exact_mod_cast Nat.factorial_le_pow n`. Use `a.trans (pow_le_pow_left₀ (Nat.cast_nonneg n) ?_ n)` and prove the remaining obligations. Use `Real.pi_gt_three` as an intermediate fact. Establish `hn : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h3 : Real.exp (ρ * S) = Real.exp (π * S) * Real.exp (2 * π * S) ^ n`. Rewrite using `[← Real.exp_nat_mul, ← Real.exp_add, hρ]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_hurwitz_le (n : ℕ) {S : ℝ} {z : ℂ} (hz : ‖z‖ ≤ S) :
    n.factorial * ‖hurwitz n z‖ ≤ 2 * Real.exp (π * S) * Real.exp (2 * π * S) ^ n := by
  set ρ : ℝ := (2 * n + 1) * π with hρ
  have hρ0 : 0 < ρ := radius_pos n
  have h1 : ‖hurwitz n z‖ ≤ ρ * (1 / ρ ^ (n + 1) * (Real.exp (ρ * S) / (1 / 2))) := by
    unfold hurwitz
    rw [← smul_eq_mul]
    apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρ0.le
    intro w hw
    have hw' : ‖w‖ = ρ := by simpa using hw
    rw [norm_smul, norm_div, norm_div, norm_pow, sub_zero, hw', norm_one]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine div_le_div₀ (by positivity) ?_ (by norm_num) (half_le_norm_exp_sub_one n hw')
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
    rw [norm_mul, hw']
    exact mul_le_mul_of_nonneg_left hz hρ0.le
  have h2 : (n.factorial : ℝ) ≤ ρ ^ n := by
    have a : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    refine a.trans (pow_le_pow_left₀ (Nat.cast_nonneg n) ?_ n)
    have := Real.pi_gt_three
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have h3 : Real.exp (ρ * S) = Real.exp (π * S) * Real.exp (2 * π * S) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, hρ]; congr 1; ring
  calc n.factorial * ‖hurwitz n z‖
      ≤ ρ ^ n * (ρ * (1 / ρ ^ (n + 1) * (Real.exp (ρ * S) / (1 / 2)))) :=
        mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
    _ = _ := by rw [h3, pow_succ]; field_simp

noncomputable def guichard (α : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, iteratedDeriv n α 0 * hurwitz n z

/- English proof (translation)
Establish `hR : 0 < 2 * Real.exp (2 * π * S)` using `by positivity`. Establish `h1` using `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hα.diffContOnCl hC`. Establish `hC0 : 0 ≤ C` using `(norm_nonneg _).trans (hC _ (circleMap_mem_sphere 0 hR.le 0))`. Establish `h2` using `norm_hurwitz_le n hz`. Rewrite using `[norm_mul]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_term_le {α : ℂ → ℂ} (hα : Differentiable ℂ α) {S C : ℝ}
    (hC : ∀ ζ ∈ Metric.sphere (0 : ℂ) (2 * Real.exp (2 * π * S)), ‖α ζ‖ ≤ C) (n : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ S) :
    ‖iteratedDeriv n α 0 * hurwitz n z‖ ≤ C * (2 * Real.exp (π * S)) * (1 / 2) ^ n := by
  have hR : 0 < 2 * Real.exp (2 * π * S) := by positivity
  have h1 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
    hα.diffContOnCl hC
  have hC0 : 0 ≤ C := (norm_nonneg _).trans
    (hC _ (circleMap_mem_sphere 0 hR.le 0))
  have h2 := norm_hurwitz_le n hz
  rw [norm_mul]
  calc _ ≤ (n.factorial * C / (2 * Real.exp (2 * π * S)) ^ n) * ‖hurwitz n z‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = (C / (2 * Real.exp (2 * π * S)) ^ n) * (n.factorial * ‖hurwitz n z‖) := by ring
    _ ≤ (C / (2 * Real.exp (2 * π * S)) ^ n) *
        (2 * Real.exp (π * S) * Real.exp (2 * π * S) ^ n) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by rw [mul_pow, one_div, inv_pow]; field_simp

/- English proof (translation)
Take `⟨C, hC⟩` from `(isCompact_sphere (0 : ℂ) (2 * Real.exp (2 * π * ‖z‖))).exists_bound_of_continuousOn hα.continuous.continuousOn`. Conclude with `Summable.of_norm_bounded (summable_geometric_two.mul_left _) fun n => norm_term_le hα hC n le_rfl`.
-/
theorem summable_term {α : ℂ → ℂ} (hα : Differentiable ℂ α) (z : ℂ) :
    Summable fun n : ℕ => iteratedDeriv n α 0 * hurwitz n z := by
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) (2 * Real.exp (2 * π * ‖z‖))).exists_bound_of_continuousOn
    hα.continuous.continuousOn
  exact Summable.of_norm_bounded (summable_geometric_two.mul_left _)
    fun n => norm_term_le hα hC n le_rfl

/- English proof (translation)
Establish `h` using `(summable_term hα z).hasSum.add (Complex.hasSum_taylorSeries_of_entire hα 0 z)`. Use `HasSum.tsum_eq ?_` and prove the remaining obligations. Establish `e : (fun n : ℕ => iteratedDeriv n α 0 * hurwitz n (z + 1)) = fun n : ℕ => iteratedDeriv n α 0 * hurwitz n z + (n.factorial : ℂ)⁻¹ • (z - 0) ^ n • iteratedDeriv n α 0`. Use function extensionality and compare the values at `n`. Rewrite using `[hurwitz_add_one]`.

Simplify using `only [smul_eq_mul, sub_zero]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h`.
-/
theorem guichard_add_one {α : ℂ → ℂ} (hα : Differentiable ℂ α) (z : ℂ) :
    guichard α (z + 1) = guichard α z + α z := by
  have h := (summable_term hα z).hasSum.add (Complex.hasSum_taylorSeries_of_entire hα 0 z)
  refine HasSum.tsum_eq ?_
  have e : (fun n : ℕ => iteratedDeriv n α 0 * hurwitz n (z + 1)) = fun n : ℕ =>
      iteratedDeriv n α 0 * hurwitz n z +
        (n.factorial : ℂ)⁻¹ • (z - 0) ^ n • iteratedDeriv n α 0 := by
    funext n
    rw [hurwitz_add_one]
    simp only [smul_eq_mul, sub_zero]
    ring
  rw [e]
  exact h

/- English proof (translation)
Establish `hO : IsOpen (X ×ˢ (Set.univ : Set ℂ))` using `hX.prod isOpen_univ`. Establish `hent : ∀ x ∈ X, Differentiable ℂ fun ζ => F (x, ζ)` using `fun x hx ζ => (hF.differentiableAt (hO.mem_nhds ⟨hx, trivial⟩)).comp ζ (by fun_prop)`. Use `(GlobalTheory.SCV.differentiableOn_tsum_of_normal_on_compacts (F := fun n x => iteratedDeriv n (fun ζ => F (x, ζ)) 0 * hurwitz n (l x)) hX ?_ ?_).1` and prove the remaining obligations. Introduce `n`. Use `DifferentiableOn.mul ?_ ((differentiable_hurwitz n).comp hl).differentiableOn` and prove the remaining obligations.

Establish `h1 : DifferentiableOn ℂ (fun x : V => iteratedFDeriv ℂ n F (x, 0)) X` using `(GlobalTheory.SCV.differentiableOn_iteratedFDeriv hO hF n).comp (f := fun x : V => (x, (0 : ℂ))) (by fun_prop) fun x hx => ⟨hx, trivial⟩`. Establish `h2` using `(ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => V × ℂ) ℂ (fun _ => ((0 : V), (1 : ℂ)))).differentiable.comp_differentiableOn h1`. Use `h2.congr fun x hx => ?_` and prove the remaining obligations. Establish `h3` using `GlobalTheory.SCV.iteratedDeriv_line hO hF (c := (x, 0)) ⟨hx, trivial⟩ ((0 : V), (1 : ℂ)) n`. Simplify using `using h3`.

Introduce `K hK hKc`. Take `⟨S, hS⟩` from `hKc.exists_bound_of_continuousOn hl.continuous.continuousOn`. Take `⟨C, hC⟩` from `(hKc.prod (isCompact_sphere (0 : ℂ) (2 * Real.exp (2 * π * S)))).exists_bound_of_continuousOn (hF.continuousOn.mono (Set.prod_mono hK (Set.subset_univ _)))`. Conclude with `⟨_, summable_geometric_two.mul_left _, fun n x hx => norm_term_le (hent x (hK hx)) (fun ζ hζ => hC (x, ζ) ⟨hx, hζ⟩) n (hS x hx)⟩`.
-/
theorem differentiableOn_guichard {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {X : Set V} (hX : IsOpen X) {F : V × ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (X ×ˢ Set.univ)) {l : V → ℂ} (hl : Differentiable ℂ l) :
    DifferentiableOn ℂ (fun x => guichard (fun ζ => F (x, ζ)) (l x)) X := by
  have hO : IsOpen (X ×ˢ (Set.univ : Set ℂ)) := hX.prod isOpen_univ
  have hent : ∀ x ∈ X, Differentiable ℂ fun ζ => F (x, ζ) := fun x hx ζ =>
    (hF.differentiableAt (hO.mem_nhds ⟨hx, trivial⟩)).comp ζ (by fun_prop)
  refine (GlobalTheory.SCV.differentiableOn_tsum_of_normal_on_compacts
    (F := fun n x => iteratedDeriv n (fun ζ => F (x, ζ)) 0 * hurwitz n (l x)) hX ?_ ?_).1
  · intro n
    refine DifferentiableOn.mul ?_ ((differentiable_hurwitz n).comp hl).differentiableOn
    have h1 : DifferentiableOn ℂ (fun x : V => iteratedFDeriv ℂ n F (x, 0)) X :=
      (GlobalTheory.SCV.differentiableOn_iteratedFDeriv hO hF n).comp (f := fun x : V => (x, (0 : ℂ)))
        (by fun_prop) fun x hx => ⟨hx, trivial⟩
    have h2 := (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => V × ℂ) ℂ
      (fun _ => ((0 : V), (1 : ℂ)))).differentiable.comp_differentiableOn h1
    refine h2.congr fun x hx => ?_
    have h3 := GlobalTheory.SCV.iteratedDeriv_line hO hF (c := (x, 0)) ⟨hx, trivial⟩ ((0 : V), (1 : ℂ)) n
    simpa using h3
  · intro K hK hKc
    obtain ⟨S, hS⟩ := hKc.exists_bound_of_continuousOn hl.continuous.continuousOn
    obtain ⟨C, hC⟩ := (hKc.prod (isCompact_sphere (0 : ℂ)
      (2 * Real.exp (2 * π * S)))).exists_bound_of_continuousOn
      (hF.continuousOn.mono (Set.prod_mono hK (Set.subset_univ _)))
    exact ⟨_, summable_geometric_two.mul_left _, fun n x hx =>
      norm_term_le (hent x (hK hx)) (fun ζ hζ => hC (x, ζ) ⟨hx, hζ⟩) n (hS x hx)⟩

section Main

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ}
  {U : Set E}

/- English proof (translation)
Establish `hO : IsOpen (cov U g)` using `hU.prod isOpen_univ`. Establish `hG : Differentiable ℂ fun Q : Pt E g × ℂ => ((Q.1.1, Function.update Q.1.2 m Q.2) : Pt E g)`. Use `Differentiable.prodMk (by fun_prop) (differentiable_pi.2 fun j => ?_)` and prove the remaining obligations. Distinguish the cases in `h : j = m`. Substitute `h` using the available equality.

Simplify using `only [Function.update_self]`. Use `fun_prop`. Simplify using `only [Function.update_of_ne h]`. Use `fun_prop`. Establish `hF : DifferentiableOn ℂ (fun Q : Pt E g × ℂ => b (Q.1.1, Function.update Q.1.2 m Q.2)) (cov U g ×ˢ Set.univ)` using `hb.comp hG.differentiableOn fun Q hQ => ⟨hQ.1.1, trivial⟩`.

Use `⟨fun P => guichard (fun ζ => b (P.1, Function.update P.2 m ζ)) (P.2 m), differentiableOn_guichard hO hF (l := fun P => P.2 m) (by fun_prop), ?_, ?_⟩` and prove the remaining obligations. Introduce `P hP`. Establish `hent : Differentiable ℂ fun ζ => b (P.1, Function.update P.2 m ζ)` using `fun ζ => (hF.differentiableAt ((hO.prod isOpen_univ).mem_nhds (x := (P, ζ)) ⟨hP, trivial⟩)).comp ζ (f := fun ζ : ℂ => (P, ζ)) (by fun_prop)`. Establish `e : ∀ ζ, Function.update (P.2 + Pi.single m 1) m ζ = Function.update P.2 m ζ`. Introduce `ζ`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = m`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne h, Pi.single_eq_of_ne h]`.

Simplify using `only [e, Pi.add_apply, Pi.single_eq_same]`. Rewrite using `[guichard_add_one hent, Function.update_eq_self]`. Introduce `k hk hper P hP`. Establish `e : ∀ ζ, b (P.1, Function.update (P.2 + Pi.single k 1) m ζ) = b (P.1, Function.update P.2 m ζ)`. Introduce `ζ`.

Rewrite using `[← hper (P.1, Function.update P.2 m ζ) ⟨hP.1, trivial⟩]`. Use `congr 2`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = m`. Substitute `h` using the available equality.

Simplify using `[Pi.single_eq_of_ne hk.symm]`. Simplify using `[Function.update_of_ne h]`. Simplify using `only [e, Pi.add_apply, Pi.single_eq_of_ne hk.symm, add_zero]`.
-/
theorem exists_solution_direction (hU : IsOpen U) (m : Fin g) {b : Pt E g → ℂ}
    (hb : DifferentiableOn ℂ b (cov U g)) :
    ∃ φ : Pt E g → ℂ, DifferentiableOn ℂ φ (cov U g) ∧
      (∀ P ∈ cov U g, φ (P.1, P.2 + Pi.single m 1) = φ P + b P) ∧
      ∀ k, k ≠ m → (∀ P ∈ cov U g, b (P.1, P.2 + Pi.single k 1) = b P) →
        ∀ P ∈ cov U g, φ (P.1, P.2 + Pi.single k 1) = φ P := by
  have hO : IsOpen (cov U g) := hU.prod isOpen_univ
  have hG : Differentiable ℂ fun Q : Pt E g × ℂ =>
      ((Q.1.1, Function.update Q.1.2 m Q.2) : Pt E g) := by
    refine Differentiable.prodMk (by fun_prop) (differentiable_pi.2 fun j => ?_)
    by_cases h : j = m
    · subst h; simp only [Function.update_self]; fun_prop
    · simp only [Function.update_of_ne h]; fun_prop
  have hF : DifferentiableOn ℂ (fun Q : Pt E g × ℂ => b (Q.1.1, Function.update Q.1.2 m Q.2))
      (cov U g ×ˢ Set.univ) :=
    hb.comp hG.differentiableOn fun Q hQ => ⟨hQ.1.1, trivial⟩
  refine ⟨fun P => guichard (fun ζ => b (P.1, Function.update P.2 m ζ)) (P.2 m),
    differentiableOn_guichard hO hF (l := fun P => P.2 m) (by fun_prop), ?_, ?_⟩
  · intro P hP
    have hent : Differentiable ℂ fun ζ => b (P.1, Function.update P.2 m ζ) := fun ζ =>
      (hF.differentiableAt ((hO.prod isOpen_univ).mem_nhds (x := (P, ζ)) ⟨hP, trivial⟩)).comp ζ
        (f := fun ζ : ℂ => (P, ζ)) (by fun_prop)
    have e : ∀ ζ, Function.update (P.2 + Pi.single m 1) m ζ = Function.update P.2 m ζ := by
      intro ζ; funext j
      by_cases h : j = m
      · subst h; simp
      · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
    simp only [e, Pi.add_apply, Pi.single_eq_same]
    rw [guichard_add_one hent, Function.update_eq_self]
  · intro k hk hper P hP
    have e : ∀ ζ, b (P.1, Function.update (P.2 + Pi.single k 1) m ζ) =
        b (P.1, Function.update P.2 m ζ) := by
      intro ζ
      rw [← hper (P.1, Function.update P.2 m ζ) ⟨hP.1, trivial⟩]
      congr 2
      funext j
      by_cases h : j = m
      · subst h; simp [Pi.single_eq_of_ne hk.symm]
      · simp [Function.update_of_ne h]
    simp only [e, Pi.add_apply, Pi.single_eq_of_ne hk.symm, add_zero]

/- English proof (translation)
Establish `key : ∀ s : Finset (Fin g), ∃ ψ : Pt E g → ℂ, DifferentiableOn ℂ ψ (cov U g) ∧ ∀ k ∈ s, ∀ P ∈ cov U g, ψ (P.1, P.2 + Pi.single k 1) = ψ P + a k P`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨fun _ => 0, differentiableOn_const _, by simp⟩`. Consider the case `insert m s hm ih`.

Take `⟨ψ, hψ, hs⟩` from `ih`. Establish `hψ' : DifferentiableOn ℂ (fun P : Pt E g => ψ (P.1, P.2 + Pi.single m 1)) (cov U g)` using `hψ.comp (f := fun P : Pt E g => ((P.1, P.2 + Pi.single m 1) : Pt E g)) (by fun_prop) fun P hP => ⟨hP.1, trivial⟩`. Take `⟨φ, hφ, h1, h2⟩` from `exists_solution_direction hU m (b := fun P => a m P - (ψ (P.1, P.2 + Pi.single m 1) - ψ P)) ((ha m).sub (hψ'.sub hψ))`. Use `⟨fun P => ψ P + φ P, hψ.add hφ, fun k hk P hP => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hk with rfl | hk` into its components or cases.

Simplify using `only [h1 P hP]`. Expand and normalize the polynomial expressions, which then agree. Establish `hkm : k ≠ m` using `fun h => hm (h ▸ hk)`. Establish `h3` using `h2 k hkm (fun Q hQ => by`. Establish `e1` using `hs k hk Q hQ`.

Establish `e2` using `hs k hk (Q.1, Q.2 + Pi.single m 1) ⟨hQ.1, trivial⟩`. Establish `e3` using `hc k m Q hQ`. Simplify using `only at e2 ⊢`. Rewrite using `[add_right_comm Q.2, e1, e2]`. Take the linear combination `-e3) P hP`.

Simplify using `only [h3, hs k hk P hP]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨ψ, h1, h2⟩` from `key Finset.univ`. Conclude with `⟨ψ, h1, fun k => h2 k (Finset.mem_univ k)⟩`.
-/
theorem exists_coboundary (hU : IsOpen U) (a : Fin g → Pt E g → ℂ)
    (ha : ∀ k, DifferentiableOn ℂ (a k) (cov U g))
    (hc : ∀ k j, ∀ P ∈ cov U g,
      a k (P.1, P.2 + Pi.single j 1) + a j P = a j (P.1, P.2 + Pi.single k 1) + a k P) :
    ∃ ψ : Pt E g → ℂ, DifferentiableOn ℂ ψ (cov U g) ∧
      ∀ k, ∀ P ∈ cov U g, ψ (P.1, P.2 + Pi.single k 1) = ψ P + a k P := by
  classical
  have key : ∀ s : Finset (Fin g), ∃ ψ : Pt E g → ℂ, DifferentiableOn ℂ ψ (cov U g) ∧
      ∀ k ∈ s, ∀ P ∈ cov U g, ψ (P.1, P.2 + Pi.single k 1) = ψ P + a k P := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => 0, differentiableOn_const _, by simp⟩
    | insert m s hm ih =>
      obtain ⟨ψ, hψ, hs⟩ := ih
      have hψ' : DifferentiableOn ℂ (fun P : Pt E g => ψ (P.1, P.2 + Pi.single m 1)) (cov U g) :=
        hψ.comp (f := fun P : Pt E g => ((P.1, P.2 + Pi.single m 1) : Pt E g)) (by fun_prop)
          fun P hP => ⟨hP.1, trivial⟩
      obtain ⟨φ, hφ, h1, h2⟩ := exists_solution_direction hU m
        (b := fun P => a m P - (ψ (P.1, P.2 + Pi.single m 1) - ψ P)) ((ha m).sub (hψ'.sub hψ))
      refine ⟨fun P => ψ P + φ P, hψ.add hφ, fun k hk P hP => ?_⟩
      rcases Finset.mem_insert.1 hk with rfl | hk
      · simp only [h1 P hP]; ring
      · have hkm : k ≠ m := fun h => hm (h ▸ hk)
        have h3 := h2 k hkm (fun Q hQ => by
          have e1 := hs k hk Q hQ
          have e2 := hs k hk (Q.1, Q.2 + Pi.single m 1) ⟨hQ.1, trivial⟩
          have e3 := hc k m Q hQ
          simp only at e2 ⊢
          rw [add_right_comm Q.2, e1, e2]
          linear_combination -e3) P hP
        simp only [h3, hs k hk P hP]; ring
  obtain ⟨ψ, h1, h2⟩ := key Finset.univ
  exact ⟨ψ, h1, fun k => h2 k (Finset.mem_univ k)⟩

end Main

/- English proof (translation)
Introduce `E _ _ _ g U hU a ha hc b₀ hb₀`. Take `⟨r, hr, hrU⟩` from `Metric.isOpen_iff.1 hU b₀ hb₀`. Take `⟨ψ, h1, h2⟩` from `exists_coboundary hU a ha hc`. Establish `hsub : cov (Metric.ball b₀ r) g ⊆ cov U g` using `fun P hP => ⟨hrU hP.1, trivial⟩`. Conclude with `⟨r, hr, hrU, ψ, h1.mono hsub, fun k P hP => h2 k P (hsub hP)⟩`.
-/
theorem main : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} {U : Set E}, IsOpen U → ∀ a : Fin g → Pt E g → ℂ, (∀ k, DifferentiableOn ℂ (a k) (cov U g)) → (∀ k j, ∀ P ∈ cov U g, a k (P.1, P.2 + Pi.single j 1) + a j P = a j (P.1, P.2 + Pi.single k 1) + a k P) → ∀ b₀ ∈ U, ∃ r > 0, Metric.ball b₀ r ⊆ U ∧ ∃ ψ : Pt E g → ℂ, DifferentiableOn ℂ ψ (cov (Metric.ball b₀ r) g) ∧ ∀ k, ∀ P ∈ cov (Metric.ball b₀ r) g, ψ (P.1, P.2 + Pi.single k 1) = ψ P + a k P := by
  intro E _ _ _ g U hU a ha hc b₀ hb₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU b₀ hb₀
  obtain ⟨ψ, h1, h2⟩ := exists_coboundary hU a ha hc
  have hsub : cov (Metric.ball b₀ r) g ⊆ cov U g := fun P hP => ⟨hrU hP.1, trivial⟩
  exact ⟨r, hr, hrU, ψ, h1.mono hsub, fun k P hP => h2 k P (hsub hP)⟩

end GlobalTheory.RealPeriodCocycle
