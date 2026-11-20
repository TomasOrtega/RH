import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

noncomputable section

open Filter Topology Asymptotics
open scoped ZeroAtInfty

namespace GlobalTheory.CompanionTheory.WaveCurve

open PositivityTheory.RgBcC.Fc

local notation "sg(" y ")" => (((y : ℝ) : ℂ) ^ (1 / 2 : ℂ))

/- English proof (translation)
Break down `le_total 0 y with hy | hy` into its components or cases. Establish `h1 : max y 0 = y` using `max_eq_left hy`. Establish `h2 : max (-y) 0 = 0` using `max_eq_right (by linarith)`. Rewrite using `[h1, h2, Real.sqrt_zero, Real.sqrt_eq_rpow, Complex.ofReal_cpow hy]`. Simplify using the standard rewrite rules.

Establish `h1 : max y 0 = 0` using `max_eq_right hy`. Establish `h2 : max (-y) 0 = -y` using `max_eq_left (by linarith)`. Establish `hy' : 0 ≤ -y` using `by linarith`. Rewrite using `[h1, h2, Real.sqrt_zero, Complex.ofReal_cpow_of_nonpos hy, Real.sqrt_eq_rpow, Complex.ofReal_cpow hy']`. Establish `: Complex.exp (Real.pi * Complex.I * (1 / 2)) = Complex.I`.

Establish `: (Real.pi : ℂ) * Complex.I * (1 / 2) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`. Rewrite using `[this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
lemma sg_eq (y : ℝ) :
    sg(y) = (Real.sqrt (max y 0) : ℂ) + (Real.sqrt (max (-y) 0) : ℂ) * Complex.I := by
  rcases le_total 0 y with hy | hy
  · have h1 : max y 0 = y := max_eq_left hy
    have h2 : max (-y) 0 = 0 := max_eq_right (by linarith)
    rw [h1, h2, Real.sqrt_zero, Real.sqrt_eq_rpow, Complex.ofReal_cpow hy]
    simp
  · have h1 : max y 0 = 0 := max_eq_right hy
    have h2 : max (-y) 0 = -y := max_eq_left (by linarith)
    have hy' : 0 ≤ -y := by linarith
    rw [h1, h2, Real.sqrt_zero, Complex.ofReal_cpow_of_nonpos hy, Real.sqrt_eq_rpow,
      Complex.ofReal_cpow hy']
    have : Complex.exp (Real.pi * Complex.I * (1 / 2)) = Complex.I := by
      have : (Real.pi : ℂ) * Complex.I * (1 / 2) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp
    rw [this]
    simp

/- English proof (translation)
Establish `: (fun y : ℝ => sg(y)) = fun y : ℝ => (Real.sqrt (max y 0) : ℂ) + (Real.sqrt (max (-y) 0) : ℂ) * Complex.I` using `funext sg_eq`. Rewrite using `[this]`. Use `fun_prop`.
-/
lemma sg_continuous : Continuous fun y : ℝ => sg(y) := by
  have : (fun y : ℝ => sg(y)) = fun y : ℝ =>
      (Real.sqrt (max y 0) : ℂ) + (Real.sqrt (max (-y) 0) : ℂ) * Complex.I := funext sg_eq
  rw [this]
  fun_prop

/- English proof (translation)
Rewrite using `[sg_eq]`. Simplify using the standard rewrite rules.
-/
lemma sg_re (y : ℝ) : (sg(y)).re = Real.sqrt (max y 0) := by
  rw [sg_eq]; simp

/- English proof (translation)
Establish `h : (sg(y)) ^ 2 = (y : ℂ)`. Use `Complex.cpow_nat_inv_pow (y : ℂ) (n := 2) (by norm_num)` as an intermediate fact. Simplify using `using this`. Rewrite using `[← norm_pow, h, Complex.norm_real, Real.norm_eq_abs]`.
-/
lemma sg_norm_sq (y : ℝ) : ‖sg(y)‖ ^ 2 = |y| := by
  have h : (sg(y)) ^ 2 = (y : ℂ) := by
    have := Complex.cpow_nat_inv_pow (y : ℂ) (n := 2) (by norm_num)
    simpa using this
  rw [← norm_pow, h, Complex.norm_real, Real.norm_eq_abs]

/- English proof (translation)
Rewrite using `[← sg_norm_sq y, Real.sqrt_sq (norm_nonneg _)]`.
-/
lemma sg_norm (y : ℝ) : ‖sg(y)‖ = Real.sqrt |y| := by
  rw [← sg_norm_sq y, Real.sqrt_sq (norm_nonneg _)]

/- English proof (translation)
Break down `le_total a 1 with h | h` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Apply `pow_le_pow_left₀ (pow_nonneg ha 4)` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma pow_le_one_add (a : ℝ) (ha : 0 ≤ a) {k N : ℕ} (hk : k ≤ 4 * N) :
    a ^ k ≤ (1 + a ^ 4) ^ N := by
  rcases le_total a 1 with h | h
  · calc a ^ k ≤ 1 := pow_le_one₀ ha h
      _ ≤ (1 + a ^ 4) ^ N := one_le_pow₀ (by nlinarith [pow_nonneg ha 4])
  · calc a ^ k ≤ a ^ (4 * N) := pow_le_pow_right₀ h hk
      _ = (a ^ 4) ^ N := pow_mul a 4 N
      _ ≤ (1 + a ^ 4) ^ N := by
        apply pow_le_pow_left₀ (pow_nonneg ha 4); linarith

/- English proof (translation)
Establish `h` using `pow_le_one_add ‖sg(y)‖ (norm_nonneg _) hk`. Establish `h4 : ‖sg(y)‖ ^ 4 = y ^ 2`. Establish `: ‖sg(y)‖ ^ 4 = (‖sg(y)‖ ^ 2) ^ 2` using `by ring`. Rewrite using `[this, sg_norm_sq, sq_abs]`. Rewrite `h` using `[h4]`. Then use the resulting hypothesis.
-/
lemma sg_pow_le (y : ℝ) {k N : ℕ} (hk : k ≤ 4 * N) : ‖sg(y)‖ ^ k ≤ (1 + y ^ 2) ^ N := by
  have h := pow_le_one_add ‖sg(y)‖ (norm_nonneg _) hk
  have h4 : ‖sg(y)‖ ^ 4 = y ^ 2 := by
    have : ‖sg(y)‖ ^ 4 = (‖sg(y)‖ ^ 2) ^ 2 := by ring
    rw [this, sg_norm_sq, sq_abs]
  rwa [h4] at h

/- English proof (translation)
The claim follows from `le_max_left _ _`.
-/
lemma cut_nonneg (c y : ℝ) : 0 ≤ cut c y := le_max_left _ _

/- English proof (translation)
The claim follows from `max_le zero_le_one (min_le_left _ _)`.
-/
lemma cut_le_one (c y : ℝ) : cut c y ≤ 1 := max_le zero_le_one (min_le_left _ _)

/- English proof (translation)
The claim follows from `max_eq_left ((min_le_right _ _).trans (by linarith))`.
-/
lemma cut_eq_zero {c y : ℝ} (h : c + 1 ≤ y) : cut c y = 0 :=
  max_eq_left ((min_le_right _ _).trans (by linarith))

/- English proof (translation)
Unfold `cut`. Use `fun_prop`.
-/
lemma cut_continuous (c : ℝ) : Continuous (cut c) := by
  unfold cut; fun_prop

/- English proof (translation)
Establish `h : Complex.cosh w = (Complex.exp w + Complex.exp (-w)) / 2`. Rewrite using `[← Complex.two_cosh]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, norm_div, Complex.norm_ofNat]`. Establish `h1` using `norm_add_le (Complex.exp w) (Complex.exp (-w))`.

Rewrite `h1` using `[Complex.norm_exp, Complex.norm_exp, Complex.neg_re]`. Establish `h2 : Real.exp w.re ≤ Real.exp |w.re|` using `Real.exp_le_exp.2 (le_abs_self _)`. Establish `h3 : Real.exp (-w.re) ≤ Real.exp |w.re|` using `Real.exp_le_exp.2 (neg_le_abs _)`. Combine the linear relations using `[h1, h2, h3]`.
-/
lemma norm_cosh_le (w : ℂ) : ‖Complex.cosh w‖ ≤ Real.exp |w.re| := by
  have h : Complex.cosh w = (Complex.exp w + Complex.exp (-w)) / 2 := by
    rw [← Complex.two_cosh]; ring
  rw [h, norm_div, Complex.norm_ofNat]
  have h1 := norm_add_le (Complex.exp w) (Complex.exp (-w))
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at h1
  have h2 : Real.exp w.re ≤ Real.exp |w.re| := Real.exp_le_exp.2 (le_abs_self _)
  have h3 : Real.exp (-w.re) ≤ Real.exp |w.re| := Real.exp_le_exp.2 (neg_le_abs _)
  linarith [h1, h2, h3]

/- English proof (translation)
Establish `h : Complex.sinh w = (Complex.exp w - Complex.exp (-w)) / 2`. Rewrite using `[← Complex.two_sinh]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, norm_div, Complex.norm_ofNat]`. Establish `h1` using `norm_sub_le (Complex.exp w) (Complex.exp (-w))`.

Rewrite `h1` using `[Complex.norm_exp, Complex.norm_exp, Complex.neg_re]`. Establish `h2 : Real.exp w.re ≤ Real.exp |w.re|` using `Real.exp_le_exp.2 (le_abs_self _)`. Establish `h3 : Real.exp (-w.re) ≤ Real.exp |w.re|` using `Real.exp_le_exp.2 (neg_le_abs _)`. Combine the linear relations using `[h1, h2, h3]`.
-/
lemma norm_sinh_le (w : ℂ) : ‖Complex.sinh w‖ ≤ Real.exp |w.re| := by
  have h : Complex.sinh w = (Complex.exp w - Complex.exp (-w)) / 2 := by
    rw [← Complex.two_sinh]; ring
  rw [h, norm_div, Complex.norm_ofNat]
  have h1 := norm_sub_le (Complex.exp w) (Complex.exp (-w))
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at h1
  have h2 : Real.exp w.re ≤ Real.exp |w.re| := Real.exp_le_exp.2 (le_abs_self _)
  have h3 : Real.exp (-w.re) ≤ Real.exp |w.re| := Real.exp_le_exp.2 (neg_le_abs _)
  linarith [h1, h2, h3]

/- English proof (translation)
Establish `hre : |((t : ℂ) * sg(y)).re| = |t| * Real.sqrt (max y 0)`. Rewrite using `[Complex.re_ofReal_mul, sg_re, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]`. Rewrite using `[← hre]`. Use `split_ifs`. Conclude with `norm_cosh_le _`.

Conclude with `norm_sinh_le _`.
-/
lemma hyp_le (j : ℕ) (t y : ℝ) :
    ‖(if Even j then Complex.cosh else Complex.sinh) ((t : ℂ) * sg(y))‖ ≤
      Real.exp (|t| * Real.sqrt (max y 0)) := by
  have hre : |((t : ℂ) * sg(y)).re| = |t| * Real.sqrt (max y 0) := by
    rw [Complex.re_ofReal_mul, sg_re, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [← hre]
  split_ifs
  · exact norm_cosh_le _
  · exact norm_sinh_le _

/- English proof (translation)
Unfold `wv chj`. Rewrite using `[norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_assoc]`. Use `hyp_le j t y` as an intermediate fact. Use `gcongr`.
-/
lemma norm_wv_le (c : ℝ) (N j : ℕ) (t y : ℝ) :
    ‖wv c N j t y‖ ≤ |cut c y * ((1 + y ^ 2) ^ N)⁻¹| * ‖sg(y)‖ ^ j *
      Real.exp (|t| * Real.sqrt (max y 0)) := by
  unfold wv chj
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
  have := hyp_le j t y
  gcongr

/- English proof (translation)
The claim follows from `|cut c y * ((1 + y ^ 2) ^ N)⁻¹| * ‖sg(y)‖ ^ k * Real.exp (|t| * Real.sqrt (max y 0)) ≤ Real.exp (|t| * Real.sqrt (max (c + 1) 0)) := by rcases le_or_gt (c + 1) y with h | h · rw [cut_eq_zero h] simp only [zero_mul, abs_zero] positivity · have hP : 0 < (1 + y ^ 2) ^ N := by positi …`.
-/
lemma base_le (c : ℝ) {N k : ℕ} (hk : k ≤ 4 * N) (t y : ℝ) :
    |cut c y * ((1 + y ^ 2) ^ N)⁻¹| * ‖sg(y)‖ ^ k * Real.exp (|t| * Real.sqrt (max y 0)) ≤
      Real.exp (|t| * Real.sqrt (max (c + 1) 0)) := by
  rcases le_or_gt (c + 1) y with h | h
  · rw [cut_eq_zero h]
    simp only [zero_mul, abs_zero]
    positivity
  · have hP : 0 < (1 + y ^ 2) ^ N := by positivity
    have hW : |cut c y * ((1 + y ^ 2) ^ N)⁻¹| ≤ ((1 + y ^ 2) ^ N)⁻¹ := by
      rw [abs_of_nonneg (mul_nonneg (cut_nonneg _ _) (inv_nonneg.2 hP.le))]
      exact mul_le_of_le_one_left (inv_nonneg.2 hP.le) (cut_le_one _ _)
    have h1 : |cut c y * ((1 + y ^ 2) ^ N)⁻¹| * ‖sg(y)‖ ^ k ≤ 1 := by
      calc _ ≤ ((1 + y ^ 2) ^ N)⁻¹ * (1 + y ^ 2) ^ N := by
            apply mul_le_mul hW (sg_pow_le y hk) (by positivity) (by positivity)
        _ = 1 := inv_mul_cancel₀ hP.ne'
    have h2 : Real.exp (|t| * Real.sqrt (max y 0)) ≤
        Real.exp (|t| * Real.sqrt (max (c + 1) 0)) := by
      apply Real.exp_le_exp.2
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact Real.sqrt_le_sqrt (max_le_max_right _ h.le)
    calc _ ≤ 1 * Real.exp (|t| * Real.sqrt (max (c + 1) 0)) := by
          apply mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = _ := one_mul _

/- English proof (translation)
The claim follows from `(norm_wv_le c N j t y).trans (base_le c hj t y)`.
-/
lemma wv_bound (c : ℝ) {N j : ℕ} (hj : j ≤ 4 * N) (t y : ℝ) :
    ‖wv c N j t y‖ ≤ Real.exp (|t| * Real.sqrt (max (c + 1) 0)) :=
  (norm_wv_le c N j t y).trans (base_le c hj t y)

/- English proof (translation)
Use `set B := Real.exp (|t| * Real.sqrt (max (c + 1) 0)) with hB`. Establish `h0 : ‖wv c N j t y‖ ≤ B` using `wv_bound c (by omega) t y`. Establish `h1 : ‖wv c N j t y‖ * ‖sg(y)‖ ≤ B`. Use `le_trans ?_ (base_le c hj t y)` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_right (norm_wv_le c N j t y) (norm_nonneg (sg(y)))` as an intermediate fact.

Use `this.trans (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[sg_norm]`. Establish `hp : 0 < 1 + Real.sqrt |y|` using `by positivity`. Rewrite using `[← div_eq_mul_inv, le_div_iff₀ hp]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
lemma wv_decay (c : ℝ) {N j : ℕ} (hj : j + 1 ≤ 4 * N) (t y : ℝ) :
    ‖wv c N j t y‖ ≤ 2 * Real.exp (|t| * Real.sqrt (max (c + 1) 0)) * (1 + Real.sqrt |y|)⁻¹ := by
  set B := Real.exp (|t| * Real.sqrt (max (c + 1) 0)) with hB
  have h0 : ‖wv c N j t y‖ ≤ B := wv_bound c (by omega) t y
  have h1 : ‖wv c N j t y‖ * ‖sg(y)‖ ≤ B := by
    refine le_trans ?_ (base_le c hj t y)
    have := mul_le_mul_of_nonneg_right (norm_wv_le c N j t y) (norm_nonneg (sg(y)))
    refine this.trans (le_of_eq ?_)
    ring
  rw [sg_norm] at h1
  have hp : 0 < 1 + Real.sqrt |y| := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  nlinarith

/- English proof (translation)
Establish `hW : Continuous fun y : ℝ => cut c y * ((1 + y ^ 2) ^ N)⁻¹`. Use `(cut_continuous c).mul (Continuous.inv₀ (by fun_prop) fun y => ?_)` and prove the remaining obligations. Check the signs of the components of the expression. Establish `hs` using `sg_continuous`. Establish `hH : Continuous fun y : ℝ => (if Even j then Complex.cosh else Complex.sinh) ((t : ℂ) * sg(y))` using `by split_ifs`.

Conclude with `Complex.continuous_cosh.comp (continuous_const.mul hs)`. Conclude with `Complex.continuous_sinh.comp (continuous_const.mul hs)`. Unfold `wv chj`. Conclude with `(Complex.continuous_ofReal.comp hW).mul ((hs.pow j).mul hH)`.
-/
lemma wv_continuous (c : ℝ) (N j : ℕ) (t : ℝ) : Continuous (wv c N j t) := by
  have hW : Continuous fun y : ℝ => cut c y * ((1 + y ^ 2) ^ N)⁻¹ := by
    refine (cut_continuous c).mul (Continuous.inv₀ (by fun_prop) fun y => ?_)
    positivity
  have hs := sg_continuous
  have hH : Continuous fun y : ℝ =>
      (if Even j then Complex.cosh else Complex.sinh) ((t : ℂ) * sg(y)) := by
    split_ifs
    · exact Complex.continuous_cosh.comp (continuous_const.mul hs)
    · exact Complex.continuous_sinh.comp (continuous_const.mul hs)
  unfold wv chj
  exact (Complex.continuous_ofReal.comp hW).mul ((hs.pow j).mul hH)

/- English proof (translation)
Use `squeeze_zero_norm (fun y => wv_decay c hj t y) ?_` and prove the remaining obligations. Establish `h1 : Tendsto (fun y : ℝ => 1 + Real.sqrt |y|) (cocompact ℝ) atTop`. Use `tendsto_atTop_add_const_left _ _ (Real.tendsto_sqrt_atTop.comp ?_)` and prove the remaining obligations. Conclude with `tendsto_norm_cocompact_atTop (E := ℝ)`. Simplify using `using (tendsto_inv_atTop_zero.comp h1).const_mul (2 * Real.exp (|t| * Real.sqrt (max (c + 1) 0)))`.
-/
lemma wv_tendsto (c : ℝ) {N j : ℕ} (hj : j + 1 ≤ 4 * N) (t : ℝ) :
    Tendsto (wv c N j t) (cocompact ℝ) (𝓝 0) := by
  refine squeeze_zero_norm (fun y => wv_decay c hj t y) ?_
  have h1 : Tendsto (fun y : ℝ => 1 + Real.sqrt |y|) (cocompact ℝ) atTop := by
    refine tendsto_atTop_add_const_left _ _ (Real.tendsto_sqrt_atTop.comp ?_)
    exact tendsto_norm_cocompact_atTop (E := ℝ)
  simpa using (tendsto_inv_atTop_zero.comp h1).const_mul
    (2 * Real.exp (|t| * Real.sqrt (max (c + 1) 0)))

/- English proof (translation)
Simplify using `only [chj]`. Generalize the expression as in `sg(y) = s`. Distinguish the cases in `hj : Even j`. Establish `h1 : ¬ Even (j + 1)` using `by simpa [Nat.even_add_one] using hj`. Simplify using `only [if_pos hj, if_neg h1]`.

Establish `h2 : HasDerivAt (fun z : ℂ => Complex.cosh (z * s)) (Complex.sinh ((t : ℂ) * s) * s) (t : ℂ)`. Establish `h0 : HasDerivAt (fun z : ℂ => z * s) s (t : ℂ)`. Simplify using `using (hasDerivAt_id (t : ℂ)).mul_const s`. Conclude with `(Complex.hasDerivAt_cosh ((t : ℂ) * s)).comp (t : ℂ) h0`. Establish `h3` using `(h2.comp_ofReal).const_mul (s ^ j)`.

Establish `e : s ^ (j + 1) * Complex.sinh ((t : ℂ) * s) = s ^ j * (Complex.sinh ((t : ℂ) * s) * s)` using `by ring`. Rewrite using `[e]`. Conclude with `h3`. Establish `h1 : Even (j + 1)` using `by simpa [Nat.even_add_one] using hj`. Simplify using `only [if_neg hj, if_pos h1]`.

Establish `h2 : HasDerivAt (fun z : ℂ => Complex.sinh (z * s)) (Complex.cosh ((t : ℂ) * s) * s) (t : ℂ)`. Establish `h0 : HasDerivAt (fun z : ℂ => z * s) s (t : ℂ)`. Simplify using `using (hasDerivAt_id (t : ℂ)).mul_const s`. Conclude with `(Complex.hasDerivAt_sinh ((t : ℂ) * s)).comp (t : ℂ) h0`. Establish `h3` using `(h2.comp_ofReal).const_mul (s ^ j)`.

Establish `e : s ^ (j + 1) * Complex.cosh ((t : ℂ) * s) = s ^ j * (Complex.cosh ((t : ℂ) * s) * s)` using `by ring`. Rewrite using `[e]`. Conclude with `h3`.
-/
lemma chj_hasDerivAt (j : ℕ) (t y : ℝ) :
    HasDerivAt (fun τ : ℝ => chj j τ y) (chj (j + 1) t y) t := by
  simp only [chj]
  generalize sg(y) = s
  by_cases hj : Even j
  · have h1 : ¬ Even (j + 1) := by simpa [Nat.even_add_one] using hj
    simp only [if_pos hj, if_neg h1]
    have h2 : HasDerivAt (fun z : ℂ => Complex.cosh (z * s))
        (Complex.sinh ((t : ℂ) * s) * s) (t : ℂ) := by
      have h0 : HasDerivAt (fun z : ℂ => z * s) s (t : ℂ) := by
        simpa using (hasDerivAt_id (t : ℂ)).mul_const s
      exact (Complex.hasDerivAt_cosh ((t : ℂ) * s)).comp (t : ℂ) h0
    have h3 := (h2.comp_ofReal).const_mul (s ^ j)
    have e : s ^ (j + 1) * Complex.sinh ((t : ℂ) * s) =
        s ^ j * (Complex.sinh ((t : ℂ) * s) * s) := by ring
    rw [e]
    exact h3
  · have h1 : Even (j + 1) := by simpa [Nat.even_add_one] using hj
    simp only [if_neg hj, if_pos h1]
    have h2 : HasDerivAt (fun z : ℂ => Complex.sinh (z * s))
        (Complex.cosh ((t : ℂ) * s) * s) (t : ℂ) := by
      have h0 : HasDerivAt (fun z : ℂ => z * s) s (t : ℂ) := by
        simpa using (hasDerivAt_id (t : ℂ)).mul_const s
      exact (Complex.hasDerivAt_sinh ((t : ℂ) * s)).comp (t : ℂ) h0
    have h3 := (h2.comp_ofReal).const_mul (s ^ j)
    have e : s ^ (j + 1) * Complex.cosh ((t : ℂ) * s) =
        s ^ j * (Complex.cosh ((t : ℂ) * s) * s) := by ring
    rw [e]
    exact h3

/- English proof (translation)
The claim follows from `(chj_hasDerivAt j t y).const_mul _`.
-/
lemma wv_hasDerivAt (c : ℝ) (N j : ℕ) (t y : ℝ) :
    HasDerivAt (fun τ : ℝ => wv c N j τ y) (wv c N (j + 1) t y) t :=
  (chj_hasDerivAt j t y).const_mul _

/- English proof (translation)
Use `set M := Real.exp ((|t| + 1) * Real.sqrt (max (c + 1) 0)) with hM`. Establish `hb : ∀ τ ∈ Set.Icc (t - 1) (t + 1), ‖wv c N (j + 1 + 1) τ y‖ ≤ M`. Introduce `τ hτ`. Use `(wv_bound c hj τ y).trans (Real.exp_le_exp.2 ?_)` and prove the remaining obligations. Apply `mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)` to reduce the goal to its premises.

Establish `h1 : |τ - t| ≤ 1` using `abs_le.2 ⟨by linarith [hτ.1], by linarith [hτ.2]⟩`. Establish `h2 : |τ| ≤ |t| + |τ - t|`. Use `abs_add_le t (τ - t)` as an intermediate fact. Simplify using `using this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `ht : t ∈ Set.Icc (t - 1) (t + 1)` using `⟨by linarith, by linarith⟩`. Establish `h1 : ∀ τ ∈ Set.Icc (t - 1) (t + 1), ‖wv c N (j + 1) τ y - wv c N (j + 1) t y‖ ≤ M * |τ - t|`. Introduce `τ hτ`. Use `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun τ => wv c N (j + 1) τ y) (f' := fun τ => wv c N (j + 1 + 1) τ y) (fun x _ => (wv_hasDerivAt c N (j + 1) x y).hasDerivWithinAt) hb (convex_Icc _ _) ht hτ` as an intermediate fact. Simplify `this` using `[Real.norm_eq_abs]`.

Use `set A := wv c N (j + 1) t y with hA`. Establish `hψ : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => wv c N j τ y - (τ : ℂ) * A) (wv c N (j + 1) τ y - A) τ`. Introduce `τ`. Establish `h2 : HasDerivAt (fun τ : ℝ => (τ : ℂ) * A) A τ`. Use `((hasDerivAt_id τ).ofReal_comp).mul_const A` as an intermediate fact.

Simplify using `using this`. Conclude with `(wv_hasDerivAt c N j τ y).sub h2`. Establish `hb2 : ∀ τ ∈ Set.uIcc t (t + h), ‖wv c N (j + 1) τ y - A‖ ≤ M * |h|`. Introduce `τ hτ`. Establish `h3 : |τ - t| ≤ |h|`.

Use `Set.abs_sub_left_of_mem_uIcc hτ` as an intermediate fact. Simplify using `using this`. Establish `h4 : |τ - t| ≤ 1` using `h3.trans hh`. Establish `h5` using `abs_le.1 h4`. Use `(h1 τ ⟨by linarith [h5.1], by linarith [h5.2]⟩).trans ?_` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le`. Use `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun τ : ℝ => wv c N j τ y - (τ : ℂ) * A) (f' := fun τ => wv c N (j + 1) τ y - A) (fun x _ => (hψ x).hasDerivWithinAt) hb2 (convex_uIcc _ _) (Set.left_mem_uIcc) (Set.right_mem_uIcc)` as an intermediate fact. Establish `e1 : wv c N j (t + h) y - wv c N j t y - (h : ℂ) * A = (wv c N j (t + h) y - ((t + h : ℝ) : ℂ) * A) - (wv c N j t y - (t : ℂ) * A)` using `by push_cast; ring`. Rewrite using `[e1]`. Use `this.trans (le_of_eq ?_)` and prove the remaining obligations.

Establish `e2 : t + h - t = h` using `by ring`. Rewrite using `[e2, Real.norm_eq_abs, mul_assoc, abs_mul_abs_self]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma wv_taylor (c : ℝ) {N j : ℕ} (hj : j + 2 ≤ 4 * N) (t h y : ℝ) (hh : |h| ≤ 1) :
    ‖wv c N j (t + h) y - wv c N j t y - (h : ℂ) * wv c N (j + 1) t y‖ ≤
      Real.exp ((|t| + 1) * Real.sqrt (max (c + 1) 0)) * h ^ 2 := by
  set M := Real.exp ((|t| + 1) * Real.sqrt (max (c + 1) 0)) with hM
  have hb : ∀ τ ∈ Set.Icc (t - 1) (t + 1), ‖wv c N (j + 1 + 1) τ y‖ ≤ M := by
    intro τ hτ
    refine (wv_bound c hj τ y).trans (Real.exp_le_exp.2 ?_)
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    have h1 : |τ - t| ≤ 1 := abs_le.2 ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have h2 : |τ| ≤ |t| + |τ - t| := by
      have := abs_add_le t (τ - t)
      simpa using this
    linarith
  have ht : t ∈ Set.Icc (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have h1 : ∀ τ ∈ Set.Icc (t - 1) (t + 1),
      ‖wv c N (j + 1) τ y - wv c N (j + 1) t y‖ ≤ M * |τ - t| := by
    intro τ hτ
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun τ => wv c N (j + 1) τ y) (f' := fun τ => wv c N (j + 1 + 1) τ y)
      (fun x _ => (wv_hasDerivAt c N (j + 1) x y).hasDerivWithinAt) hb (convex_Icc _ _) ht hτ
    simpa [Real.norm_eq_abs] using this
  set A := wv c N (j + 1) t y with hA
  have hψ : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => wv c N j τ y - (τ : ℂ) * A)
      (wv c N (j + 1) τ y - A) τ := by
    intro τ
    have h2 : HasDerivAt (fun τ : ℝ => (τ : ℂ) * A) A τ := by
      have := ((hasDerivAt_id τ).ofReal_comp).mul_const A
      simpa using this
    exact (wv_hasDerivAt c N j τ y).sub h2
  have hb2 : ∀ τ ∈ Set.uIcc t (t + h), ‖wv c N (j + 1) τ y - A‖ ≤ M * |h| := by
    intro τ hτ
    have h3 : |τ - t| ≤ |h| := by
      have := Set.abs_sub_left_of_mem_uIcc hτ
      simpa using this
    have h4 : |τ - t| ≤ 1 := h3.trans hh
    have h5 := abs_le.1 h4
    refine (h1 τ ⟨by linarith [h5.1], by linarith [h5.2]⟩).trans ?_
    exact mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun τ : ℝ => wv c N j τ y - (τ : ℂ) * A) (f' := fun τ => wv c N (j + 1) τ y - A)
    (fun x _ => (hψ x).hasDerivWithinAt) hb2 (convex_uIcc _ _)
    (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have e1 : wv c N j (t + h) y - wv c N j t y - (h : ℂ) * A =
      (wv c N j (t + h) y - ((t + h : ℝ) : ℂ) * A) - (wv c N j t y - (t : ℂ) * A) := by
    push_cast; ring
  rw [e1]
  refine this.trans (le_of_eq ?_)
  have e2 : t + h - t = h := by ring
  rw [e2, Real.norm_eq_abs, mul_assoc, abs_mul_abs_self]
  ring

/- English proof (translation)
Unfold `toC0`. Rewrite using `[dif_pos (⟨h1, h2⟩ : Continuous f ∧ Tendsto f (cocompact ℝ) (𝓝 0))]`. Both sides reduce to the same expression.
-/
lemma coe_toC0 {f : ℝ → ℂ} (h1 : Continuous f) (h2 : Tendsto f (cocompact ℝ) (𝓝 0)) :
    ⇑(toC0 f) = f := by
  unfold toC0
  rw [dif_pos (⟨h1, h2⟩ : Continuous f ∧ Tendsto f (cocompact ℝ) (𝓝 0))]
  rfl

/- English proof (translation)
Introduce `c N j hj t`. Establish `hC : ∀ {k : ℕ}, k + 1 ≤ 4 * N → ∀ τ : ℝ, ⇑(toC0 (wv c N k τ)) = wv c N k τ` using `fun hk τ => coe_toC0 (wv_continuous c N _ τ) (wv_tendsto c hk τ)`. Use `⟨⟨wv_continuous c N j t, wv_tendsto c (by omega) t⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hasDerivAt_iff_isLittleO_nhds_zero]`. Establish `hO : (fun h : ℝ => toC0 (wv c N j (t + h)) - toC0 (wv c N j t) - h • toC0 (wv c N (j + 1) t)) =O[𝓝 0] fun h : ℝ => h ^ 2`.

Use `IsBigO.of_bound (Real.exp ((|t| + 1) * Real.sqrt (max (c + 1) 0))) ?_` and prove the remaining obligations. Use `filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with h hh`. Establish `hh1 : |h| ≤ 1`. Establish `: |h| < 1` using `by simpa [Real.norm_eq_abs] using hh`. Conclude with `this.le`.

Rewrite using `[← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]`. Use `(BoundedContinuousFunction.norm_le (by positivity)).2 fun y => ?_` and prove the remaining obligations. Establish `e : (toC0 (wv c N j (t + h)) - toC0 (wv c N j t) - h • toC0 (wv c N (j + 1) t)).toBCF y = wv c N j (t + h) y - wv c N j t y - (h : ℂ) * wv c N (j + 1) t y` using `by show (toC0 (wv c N j (t + h)) - toC0 (wv c N j t) - h • toC0 (wv c N (j + 1) t) : C₀(ℝ, ℂ)) y = _`. Simplify using `only [ZeroAtInftyContinuousMap.coe_sub, ZeroAtInftyContinuousMap.coe_smul, Pi.sub_apply, Pi.smul_apply, hC (k := j) (by omega), hC (k := j + 1) (by omega), Complex.real_smul]`. Rewrite using `[e]`.

Conclude with `wv_taylor c hj t h y hh1`. Use `hO.trans_isLittleO ?_` and prove the remaining obligations. Simplify using `using isLittleO_pow_id (𝕜 := ℝ) one_lt_two`.
-/
theorem fcurve : Fcurve := by
  intro c N j hj t
  have hC : ∀ {k : ℕ}, k + 1 ≤ 4 * N → ∀ τ : ℝ, ⇑(toC0 (wv c N k τ)) = wv c N k τ :=
    fun hk τ => coe_toC0 (wv_continuous c N _ τ) (wv_tendsto c hk τ)
  refine ⟨⟨wv_continuous c N j t, wv_tendsto c (by omega) t⟩, ?_⟩
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun h : ℝ => toC0 (wv c N j (t + h)) - toC0 (wv c N j t) -
      h • toC0 (wv c N (j + 1) t)) =O[𝓝 0] fun h : ℝ => h ^ 2 := by
    refine IsBigO.of_bound (Real.exp ((|t| + 1) * Real.sqrt (max (c + 1) 0))) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with h hh
    have hh1 : |h| ≤ 1 := by
      have : |h| < 1 := by simpa [Real.norm_eq_abs] using hh
      exact this.le
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg h)]
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun y => ?_
    have e : (toC0 (wv c N j (t + h)) - toC0 (wv c N j t) -
        h • toC0 (wv c N (j + 1) t)).toBCF y =
        wv c N j (t + h) y - wv c N j t y - (h : ℂ) * wv c N (j + 1) t y := by
      show (toC0 (wv c N j (t + h)) - toC0 (wv c N j t) -
        h • toC0 (wv c N (j + 1) t) : C₀(ℝ, ℂ)) y = _
      simp only [ZeroAtInftyContinuousMap.coe_sub, ZeroAtInftyContinuousMap.coe_smul,
        Pi.sub_apply, Pi.smul_apply, hC (k := j) (by omega), hC (k := j + 1) (by omega),
        Complex.real_smul]
    rw [e]
    exact wv_taylor c hj t h y hh1
  refine hO.trans_isLittleO ?_
  simpa using isLittleO_pow_id (𝕜 := ℝ) one_lt_two

end GlobalTheory.CompanionTheory.WaveCurve
