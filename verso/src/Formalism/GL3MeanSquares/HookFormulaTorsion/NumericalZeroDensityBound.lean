import Mathlib
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis
import Formalism.GL3MeanSquares.HookFormulaTorsion.WeightedVonMangoldtSumIdentity

open Filter

namespace Formalism.HermitianLattices.ZeroFreeRegionGL2

/- English proof (translation)
Establish `h1 : Asymptotics.IsLittleO atTop (fun x : ℝ => K * Real.log x ^ (k : ℝ)) (fun x => x ^ a)` using `(isLittleO_log_rpow_rpow_atTop (k : ℝ) ha).const_mul_left K`. Use `filter_upwards [h1.bound one_pos, eventually_ge_atTop (0 : ℝ)] with x hx hx0`. Rewrite `hx` using `[Real.rpow_natCast, one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 a)]`. Conclude with `le_trans (le_abs_self _) hx`.
-/
private lemma ev_log_pow (K a : ℝ) (ha : 0 < a) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, K * Real.log x ^ k ≤ x ^ a := by
  have h1 : Asymptotics.IsLittleO atTop (fun x : ℝ => K * Real.log x ^ (k : ℝ)) (fun x => x ^ a) :=
    (isLittleO_log_rpow_rpow_atTop (k : ℝ) ha).const_mul_left K
  filter_upwards [h1.bound one_pos, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [Real.rpow_natCast, one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hx0 a)] at hx
  exact le_trans (le_abs_self _) hx

/- English proof (translation)
The claim follows from `(tendsto_rpow_atTop ha).eventually_ge_atTop K`.
-/
private lemma ev_rpow_ge (K a : ℝ) (ha : 0 < a) : ∀ᶠ x : ℝ in atTop, K ≤ x ^ a := (tendsto_rpow_atTop ha).eventually_ge_atTop K

/- English proof (translation)
The claim follows from `Real.tendsto_log_atTop.eventually_ge_atTop K`.
-/
private lemma ev_log_ge (K : ℝ) : ∀ᶠ x : ℝ in atTop, K ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop K

/- English proof (translation)
Use `Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma log_eight_le_seven : Real.log 8 ≤ 7 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)
  linarith

/- English proof (translation)
The claim follows from `Real.log_nonneg (by norm_num)`.
-/
private lemma log_eight_nonneg : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)

/- English proof (translation)
Unfold `X1`. Conclude with `Real.exp_pos _`.
-/
private lemma exp_scale_pos (ε x : ℝ) : 0 < X1 ε x := by unfold X1; exact Real.exp_pos _
/- English proof (translation)
Unfold `X2`. Conclude with `Real.exp_pos _`.
-/
private lemma double_exp_scale_pos (ε x : ℝ) : 0 < X2 ε x := by unfold X2; exact Real.exp_pos _
/- English proof (translation)
Unfold `X1`. Conclude with `Real.log_exp _`.
-/
private lemma log_exp_scale (ε x : ℝ) : Real.log (X1 ε x) = x ^ (ε / 5) := by unfold X1; exact Real.log_exp _
/- English proof (translation)
Unfold `X2`. Conclude with `Real.log_exp _`.
-/
private lemma log_double_exp_scale (ε x : ℝ) : Real.log (X2 ε x) = x ^ (ε / 5) * Real.log x ^ 2 := by unfold X2; exact Real.log_exp _
/- English proof (translation)
Unfold `X1`. Rewrite using `[← Real.exp_mul]`.
-/
private lemma exp_scale_rpow (ε x a : ℝ) : X1 ε x ^ a = Real.exp (x ^ (ε / 5) * a) := by unfold X1; rw [← Real.exp_mul]
/- English proof (translation)
Unfold `X2`. Rewrite using `[← Real.exp_mul]`.
-/
private lemma double_exp_scale_rpow (ε x a : ℝ) : X2 ε x ^ a = Real.exp (x ^ (ε / 5) * Real.log x ^ 2 * a) := by unfold X2; rw [← Real.exp_mul]
/- English proof (translation)
Rewrite using `[Real.log_mul (by norm_num) (exp_scale_pos ε x).ne', log_exp_scale]`.
-/
private lemma log_8X1 (ε x : ℝ) : Real.log (8 * X1 ε x) = Real.log 8 + x ^ (ε / 5) := by
  rw [Real.log_mul (by norm_num) (exp_scale_pos ε x).ne', log_exp_scale]
/- English proof (translation)
Rewrite using `[Real.log_mul (mul_pos (by norm_num) (exp_scale_pos ε x)).ne' (double_exp_scale_pos ε x).ne', Real.log_mul (by norm_num) (exp_scale_pos ε x).ne', log_exp_scale, log_double_exp_scale]`.
-/
private lemma log_8X1X2 (ε x : ℝ) :
    Real.log (8 * X1 ε x * X2 ε x) = Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2 := by
  rw [Real.log_mul (mul_pos (by norm_num) (exp_scale_pos ε x)).ne' (double_exp_scale_pos ε x).ne',
    Real.log_mul (by norm_num) (exp_scale_pos ε x).ne', log_exp_scale, log_double_exp_scale]
/- English proof (translation)
The claim follows from `Real.rpow_def_of_pos hu a`.
-/
private lemma rpow_eq_exp_log {u : ℝ} (hu : 0 < u) (a : ℝ) : u ^ a = Real.exp (Real.log u * a) := Real.rpow_def_of_pos hu a

/- English proof (translation)
Introduce `ε C hε hε1 hC`. Establish `hε5 : 0 < ε / 5` using `by positivity`. Establish `hε20 : 0 < ε / 20` using `by positivity`. Use `Filter.eventually_atTop.mp ?_` and prove the remaining obligations. Use `filter_upwards [ev_log_pow 801 (ε / 5) hε5 1, ev_log_pow 807 (ε / 5) hε5 3, ev_log_ge 1, ev_rpow_ge 7 (ε / 5) hε5, ev_rpow_ge ((20 / 13) * (|Real.log (4 * C)| + 2)) (ε / 5) hε5, ev_rpow_ge 2 (ε / 20) hε20, ev_log_pow (4 * C) ε hε 1, ev_rpow_ge 8 ε hε, eventually_ge_atTop (1 : ℝ)] …`.

Establish `hx0 : (0 : ℝ) < x` using `by linarith`. Rewrite `hA`, `hw` using `[pow_one]`. Establish `hl8` using `log_eight_le_seven`. Establish `hl80` using `log_eight_nonneg`. Establish `hLp : 0 < Real.log x` using `by linarith`.

Establish `hL3 : 0 < Real.log x ^ 3` using `pow_pos hLp 3`. Establish `hsq7` using `mul_nonneg (sq_nonneg (Real.log x)) (sub_nonneg.mpr hl8)`. Establish `hsqL` using `mul_nonneg (sq_nonneg (Real.log x)) (sub_nonneg.mpr hL)`. Establish `hwp : 0 < x ^ ε` using `by positivity`. Use `⟨?_, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `e : Real.exp (((400 : ℕ) : ℝ) * Real.log x) = x ^ 400`. Rewrite using `[Real.exp_nat_mul, Real.exp_log hx0]`. Rewrite using `[← e, exp_scale_rpow]`. Apply `Real.exp_lt_exp.mpr` to reduce the goal to its premises. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[log_exp_scale]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hlog : Real.log (8 * (x ^ 400) ^ 2) = Real.log 8 + 800 * Real.log x`. Rewrite using `[Real.log_mul (by norm_num) (pow_pos (pow_pos hx0 400) 2).ne', Real.log_pow, Real.log_pow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[log_exp_scale, hlog]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[log_exp_scale]`.

Conclude with `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Rewrite using `[log_8X1]`. Use `Real.rpow_le_rpow_of_exponent_le hx1 (show ε / 6 ≤ ε / 5 by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[log_8X1]`.

Establish `hsp : x ^ (ε / 4) = x ^ (ε / 5) * x ^ (ε / 20)`. Rewrite using `[← Real.rpow_add hx0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsp]`.

Use polynomial arithmetic with `[mul_nonneg (by linarith : (0 : ℝ) ≤ x ^ (ε / 5)) (by linarith : (0 : ℝ) ≤ x ^ (ε / 20) - 2)]`. Establish `hsplit : x ^ (1 / 2 + ε) = x ^ (1 / 2 : ℝ) * x ^ ε` using `Real.rpow_add hx0 _ _`. Establish `hs2 : (x ^ (1 / 2 : ℝ)) ^ 2 = x`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hx0.le]`. Evaluate the numerical expressions.

Establish `hden : (x ^ (1 / 2 + ε) / 2) ^ 2 = x * (x ^ ε) ^ 2 / 4`. Rewrite using `[hsplit, div_pow, mul_pow, hs2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hden, Real.rpow_neg hx0.le, div_le_iff₀ (by positivity)]`. Establish `hwne : x ^ ε ≠ 0` using `hwp.ne'`.

Establish `hr : (x ^ ε)⁻¹ * (x * (x ^ ε) ^ 2 / 4) = x * x ^ ε / 4`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hr]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hw hx0.le]`. Rewrite using `[Real.rpow_neg hx0.le, inv_eq_one_div]`.

Conclude with `one_div_le_one_div_of_le (by norm_num) hw8`. Establish `h8X : 8 * X1 ε x = Real.exp (Real.log 8 + x ^ (ε / 5))`. Unfold `X1`. Rewrite using `[Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8)]`. Establish `hE : 4 * C * Real.exp ((Real.log 8 + x ^ (ε / 5)) * (1 / 4)) = Real.exp (Real.log (4 * C) + (Real.log 8 + x ^ (ε / 5)) * (1 / 4))`.

Rewrite using `[Real.exp_add, Real.exp_log (mul_pos (by norm_num) hC)]`. Establish `hle : Real.exp (Real.log (4 * C) + (Real.log 8 + x ^ (ε / 5)) * (1 / 4)) ≤ Real.exp (x ^ (ε / 5) * (9 / 10))`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use `le_abs_self (Real.log (4 * C))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[h8X, ← Real.exp_mul, exp_scale_rpow]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem numerical_bound_unit_modulus : UnitModulusIncrementConditions := by
  intro ε C hε hε1 hC
  have hε5 : 0 < ε / 5 := by positivity
  have hε20 : 0 < ε / 20 := by positivity
  refine Filter.eventually_atTop.mp ?_
  filter_upwards [ev_log_pow 801 (ε / 5) hε5 1, ev_log_pow 807 (ε / 5) hε5 3, ev_log_ge 1,
    ev_rpow_ge 7 (ε / 5) hε5, ev_rpow_ge ((20 / 13) * (|Real.log (4 * C)| + 2)) (ε / 5) hε5,
    ev_rpow_ge 2 (ε / 20) hε20, ev_log_pow (4 * C) ε hε 1, ev_rpow_ge 8 ε hε,
    eventually_ge_atTop (1 : ℝ)] with x hA hB hL hu7 huC hv hw hw8 hx1
  have hx0 : (0 : ℝ) < x := by linarith
  rw [pow_one] at hA hw
  have hl8 := log_eight_le_seven
  have hl80 := log_eight_nonneg
  have hLp : 0 < Real.log x := by linarith
  have hL3 : 0 < Real.log x ^ 3 := pow_pos hLp 3
  have hsq7 := mul_nonneg (sq_nonneg (Real.log x)) (sub_nonneg.mpr hl8)
  have hsqL := mul_nonneg (sq_nonneg (Real.log x)) (sub_nonneg.mpr hL)
  have hwp : 0 < x ^ ε := by positivity
  refine ⟨?_, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have e : Real.exp (((400 : ℕ) : ℝ) * Real.log x) = x ^ 400 := by
      rw [Real.exp_nat_mul, Real.exp_log hx0]
    rw [← e, exp_scale_rpow]
    apply Real.exp_lt_exp.mpr
    push_cast
    linarith
  · rw [log_exp_scale]
    nlinarith
  · have hlog : Real.log (8 * (x ^ 400) ^ 2) = Real.log 8 + 800 * Real.log x := by
      rw [Real.log_mul (by norm_num) (pow_pos (pow_pos hx0 400) 2).ne', Real.log_pow, Real.log_pow]
      push_cast
      ring
    rw [log_exp_scale, hlog]
    nlinarith
  · rw [log_exp_scale]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  · rw [log_8X1]
    have := Real.rpow_le_rpow_of_exponent_le hx1 (show ε / 6 ≤ ε / 5 by linarith)
    linarith
  · rw [log_8X1]
    have hsp : x ^ (ε / 4) = x ^ (ε / 5) * x ^ (ε / 20) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [hsp]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x ^ (ε / 5)) (by linarith : (0 : ℝ) ≤ x ^ (ε / 20) - 2)]
  · have hsplit : x ^ (1 / 2 + ε) = x ^ (1 / 2 : ℝ) * x ^ ε := Real.rpow_add hx0 _ _
    have hs2 : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    have hden : (x ^ (1 / 2 + ε) / 2) ^ 2 = x * (x ^ ε) ^ 2 / 4 := by
      rw [hsplit, div_pow, mul_pow, hs2]
      ring
    rw [hden, Real.rpow_neg hx0.le, div_le_iff₀ (by positivity)]
    have hwne : x ^ ε ≠ 0 := hwp.ne'
    have hr : (x ^ ε)⁻¹ * (x * (x ^ ε) ^ 2 / 4) = x * x ^ ε / 4 := by
      field_simp
    rw [hr]
    nlinarith [mul_le_mul_of_nonneg_left hw hx0.le]
  · rw [Real.rpow_neg hx0.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hw8
  · have h8X : 8 * X1 ε x = Real.exp (Real.log 8 + x ^ (ε / 5)) := by
      unfold X1
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
    have hE : 4 * C * Real.exp ((Real.log 8 + x ^ (ε / 5)) * (1 / 4)) =
        Real.exp (Real.log (4 * C) + (Real.log 8 + x ^ (ε / 5)) * (1 / 4)) := by
      rw [Real.exp_add, Real.exp_log (mul_pos (by norm_num) hC)]
    have hle : Real.exp (Real.log (4 * C) + (Real.log 8 + x ^ (ε / 5)) * (1 / 4)) ≤
        Real.exp (x ^ (ε / 5) * (9 / 10)) := by
      apply Real.exp_le_exp.mpr
      have := le_abs_self (Real.log (4 * C))
      linarith
    rw [h8X, ← Real.exp_mul, exp_scale_rpow]
    linarith

/- English proof (translation)
Introduce `ε C hε hε1 hC`. Establish `hε5 : 0 < ε / 5` using `by positivity`. Establish `hε20 : 0 < ε / 20` using `by positivity`. Use `Filter.eventually_atTop.mp ?_` and prove the remaining obligations. Use `filter_upwards [ev_log_ge 5, ev_rpow_ge 16 (ε / 5) hε5, ev_rpow_ge (|Real.log (8 * C)| + 2) (ε / 5) hε5, ev_log_pow 3 (ε / 20) hε20 2, ev_rpow_ge 2 (1 / 2) (by norm_num), eventually_ge_atTop (1 : ℝ)] with x hL hu16 huC hv hs hx1`.

Establish `hx0 : (0 : ℝ) < x` using `by linarith`. Establish `hl8` using `log_eight_le_seven`. Establish `hl80` using `log_eight_nonneg`. Establish `hu0 : 0 < x ^ (ε / 5)` using `by positivity`. Establish `he : x ^ (ε / 6) ≤ x ^ (ε / 5)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`.

Establish `hL2 : 25 ≤ Real.log x ^ 2` using `by nlinarith`. Establish `huL` using `mul_le_mul_of_nonneg_left hL2 hu0.le`. Establish `h8 : 8 * X1 ε x * X2 ε x = Real.exp (Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2)`. Unfold `X1 X2`. Rewrite using `[Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8)]`.

Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `m₀ hm0 hm`. Establish `h16 : Real.log 16 ≤ 15`. Use `Real.log_le_sub_one_of_pos (show (0 : ℝ) < 16 by norm_num)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlm : Real.log m₀ ≤ Real.log 16 + 3 * x ^ (ε / 5)`. Use `Real.log_le_log hm0 hm` as an intermediate fact. Rewrite `this` using `[Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]`. Then use the resulting hypothesis. Rewrite using `[log_double_exp_scale]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hlm (sq_nonneg (Real.log x)), mul_nonneg (sq_nonneg (Real.log x)) (by linarith : (0 : ℝ) ≤ x ^ (ε / 5) - Real.log 16)]`.

Rewrite using `[log_double_exp_scale]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[h8, ← Real.exp_mul, double_exp_scale_rpow]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[log_8X1X2]`. Use polynomial arithmetic with `[mul_nonneg hu0.le (sq_nonneg (Real.log x))]`. Rewrite using `[log_8X1X2]`. Establish `hsp : x ^ (ε / 4) = x ^ (ε / 5) * x ^ (ε / 20)`. Rewrite using `[← Real.rpow_add hx0]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsp]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hv hu0.le]`. Establish `hE : 8 * C * Real.exp ((Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2) * (1 / 4)) = Real.exp (Real.log (8 * C) + (Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2) * (1 / 4))`.

Rewrite using `[Real.exp_add, Real.exp_log (mul_pos (by norm_num) hC)]`. Establish `hle : Real.exp (Real.log (8 * C) + (Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2) * (1 / 4)) ≤ Real.exp (x ^ (ε / 5) * Real.log x ^ 2 * (9 / 10))`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use `le_abs_self (Real.log (8 * C))` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[h8, ← Real.exp_mul, double_exp_scale_rpow]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Real.rpow_add hx0]`. Establish `hwp : 0 < x ^ ε` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hs hwp.le]`.
-/
theorem numerical_zero_density_bound : IncrementSizeConditions := by
  intro ε C hε hε1 hC
  have hε5 : 0 < ε / 5 := by positivity
  have hε20 : 0 < ε / 20 := by positivity
  refine Filter.eventually_atTop.mp ?_
  filter_upwards [ev_log_ge 5, ev_rpow_ge 16 (ε / 5) hε5,
    ev_rpow_ge (|Real.log (8 * C)| + 2) (ε / 5) hε5, ev_log_pow 3 (ε / 20) hε20 2,
    ev_rpow_ge 2 (1 / 2) (by norm_num), eventually_ge_atTop (1 : ℝ)] with x hL hu16 huC hv hs hx1
  have hx0 : (0 : ℝ) < x := by linarith
  have hl8 := log_eight_le_seven
  have hl80 := log_eight_nonneg
  have hu0 : 0 < x ^ (ε / 5) := by positivity
  have he : x ^ (ε / 6) ≤ x ^ (ε / 5) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hL2 : 25 ≤ Real.log x ^ 2 := by nlinarith
  have huL := mul_le_mul_of_nonneg_left hL2 hu0.le
  have h8 : 8 * X1 ε x * X2 ε x =
      Real.exp (Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2) := by
    unfold X1 X2
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m₀ hm0 hm
    have h16 : Real.log 16 ≤ 15 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 16 by norm_num)
      linarith
    have hlm : Real.log m₀ ≤ Real.log 16 + 3 * x ^ (ε / 5) := by
      have := Real.log_le_log hm0 hm
      rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
    rw [log_double_exp_scale]
    nlinarith [mul_le_mul_of_nonneg_left hlm (sq_nonneg (Real.log x)),
      mul_nonneg (sq_nonneg (Real.log x)) (by linarith : (0 : ℝ) ≤ x ^ (ε / 5) - Real.log 16)]
  · rw [log_double_exp_scale]
    nlinarith
  · rw [h8, ← Real.exp_mul, double_exp_scale_rpow]
    apply Real.exp_le_exp.mpr
    nlinarith
  · rw [log_8X1X2]
    nlinarith [mul_nonneg hu0.le (sq_nonneg (Real.log x))]
  · rw [log_8X1X2]
    have hsp : x ^ (ε / 4) = x ^ (ε / 5) * x ^ (ε / 20) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [hsp]
    nlinarith [mul_le_mul_of_nonneg_left hv hu0.le]
  · have hE : 8 * C * Real.exp ((Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2) * (1 / 4)) =
        Real.exp (Real.log (8 * C) +
          (Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2) * (1 / 4)) := by
      rw [Real.exp_add, Real.exp_log (mul_pos (by norm_num) hC)]
    have hle : Real.exp (Real.log (8 * C) +
          (Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2) * (1 / 4)) ≤
        Real.exp (x ^ (ε / 5) * Real.log x ^ 2 * (9 / 10)) := by
      apply Real.exp_le_exp.mpr
      have := le_abs_self (Real.log (8 * C))
      nlinarith
    rw [h8, ← Real.exp_mul, double_exp_scale_rpow]
    linarith
  · rw [Real.rpow_add hx0]
    have hwp : 0 < x ^ ε := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hs hwp.le]

/- English proof (translation)
Introduce `ε A hε hA`. Establish `hε5 : 0 < ε / 5` using `by positivity`. Use `Filter.eventually_atTop.mp ?_` and prove the remaining obligations. Use `filter_upwards [ev_log_pow A (ε / 5) hε5 1, ev_rpow_ge 3 (ε / 5) hε5, ev_log_ge 2, eventually_ge_atTop (1 : ℝ)] with x hAL hu3 hL hx1`. Introduce `n q₁ d hn hnx hq1 hq1' hd hd'`.

Establish `hx0 : (0 : ℝ) < x` using `by linarith`. Rewrite `hAL` using `[pow_one]`. Establish `hX1h : X1 ε x ^ (1 / 2 : ℝ) = Real.exp (x ^ (ε / 5) * (1 / 2))` using `exp_scale_rpow ε x _`. Establish `hX2h : X2 ε x ^ (1 / 2 : ℝ) = Real.exp (x ^ (ε / 5) * Real.log x ^ 2 * (1 / 2))` using `double_exp_scale_rpow ε x _`. Establish `hX1p : 0 < X1 ε x ^ (1 / 2 : ℝ)` using `by rw [hX1h]; exact Real.exp_pos _`.

Establish `hX2p : 0 < X2 ε x ^ (1 / 2 : ℝ)` using `by rw [hX2h]; exact Real.exp_pos _`. Establish `hq0 : (0 : ℝ) < q₁` using `lt_trans hX1p hq1`. Establish `hd0 : (0 : ℝ) < d` using `lt_trans hX2p hd`. Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `h1 : x ^ (ε / 5) / 2 < Real.log q₁`.

Use `Real.log_lt_log hX1p hq1` as an intermediate fact. Rewrite `this` using `[hX1h, Real.log_exp]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : Real.log q₁ ≤ x ^ (ε / 5)`. Use `Real.log_le_log hq0 hq1'` as an intermediate fact.

Rewrite `this` using `[log_exp_scale]`. Then use the resulting hypothesis. Establish `h3 : x ^ (ε / 5) * Real.log x ^ 2 / 2 < Real.log d`. Use `Real.log_lt_log hX2p hd` as an intermediate fact. Rewrite `this` using `[hX2h, Real.log_exp]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h4 : Real.log d ≤ x ^ (ε / 5) * Real.log x ^ 2`. Use `Real.log_le_log hd0 hd'` as an intermediate fact. Rewrite `this` using `[log_double_exp_scale]`. Then use the resulting hypothesis. Establish `h5 : Real.log n ≤ A * Real.log x`. Use `Real.log_le_log hn0 hnx` as an intermediate fact.

Rewrite `this` using `[Real.log_rpow hx0]`. Then use the resulting hypothesis. Use `⟨h1, h2, h3, h4, ?_⟩` and prove the remaining obligations. Establish `hlog4 : Real.log 4 ≤ 3`. Use `Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hL4 : (4 : ℝ) ≤ Real.log x ^ 2` using `by nlinarith`. Establish `hu0 : (0 : ℝ) ≤ x ^ (ε / 5)` using `by positivity`. Establish `huL` using `mul_le_mul_of_nonneg_left hL4 hu0`. Use `push_cast`. Rewrite using `[Real.log_mul (mul_pos (mul_pos (show (0 : ℝ) < 4 by norm_num) hn0) hq0).ne' hd0.ne', Real.log_mul (mul_pos (show (0 : ℝ) < 4 by norm_num) hn0).ne' hq0.ne', Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num) hn0.ne']`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem log_nonexceptional_bound : LogNE := by
  intro ε A hε hA
  have hε5 : 0 < ε / 5 := by positivity
  refine Filter.eventually_atTop.mp ?_
  filter_upwards [ev_log_pow A (ε / 5) hε5 1, ev_rpow_ge 3 (ε / 5) hε5, ev_log_ge 2,
    eventually_ge_atTop (1 : ℝ)] with x hAL hu3 hL hx1
  intro n q₁ d hn hnx hq1 hq1' hd hd'
  have hx0 : (0 : ℝ) < x := by linarith
  rw [pow_one] at hAL
  have hX1h : X1 ε x ^ (1 / 2 : ℝ) = Real.exp (x ^ (ε / 5) * (1 / 2)) := exp_scale_rpow ε x _
  have hX2h : X2 ε x ^ (1 / 2 : ℝ) = Real.exp (x ^ (ε / 5) * Real.log x ^ 2 * (1 / 2)) :=
    double_exp_scale_rpow ε x _
  have hX1p : 0 < X1 ε x ^ (1 / 2 : ℝ) := by rw [hX1h]; exact Real.exp_pos _
  have hX2p : 0 < X2 ε x ^ (1 / 2 : ℝ) := by rw [hX2h]; exact Real.exp_pos _
  have hq0 : (0 : ℝ) < q₁ := lt_trans hX1p hq1
  have hd0 : (0 : ℝ) < d := lt_trans hX2p hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : x ^ (ε / 5) / 2 < Real.log q₁ := by
    have := Real.log_lt_log hX1p hq1
    rw [hX1h, Real.log_exp] at this
    linarith
  have h2 : Real.log q₁ ≤ x ^ (ε / 5) := by
    have := Real.log_le_log hq0 hq1'
    rwa [log_exp_scale] at this
  have h3 : x ^ (ε / 5) * Real.log x ^ 2 / 2 < Real.log d := by
    have := Real.log_lt_log hX2p hd
    rw [hX2h, Real.log_exp] at this
    linarith
  have h4 : Real.log d ≤ x ^ (ε / 5) * Real.log x ^ 2 := by
    have := Real.log_le_log hd0 hd'
    rwa [log_double_exp_scale] at this
  have h5 : Real.log n ≤ A * Real.log x := by
    have := Real.log_le_log hn0 hnx
    rwa [Real.log_rpow hx0] at this
  refine ⟨h1, h2, h3, h4, ?_⟩
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have hL4 : (4 : ℝ) ≤ Real.log x ^ 2 := by nlinarith
  have hu0 : (0 : ℝ) ≤ x ^ (ε / 5) := by positivity
  have huL := mul_le_mul_of_nonneg_left hL4 hu0
  push_cast
  rw [Real.log_mul (mul_pos (mul_pos (show (0 : ℝ) < 4 by norm_num) hn0) hq0).ne' hd0.ne',
    Real.log_mul (mul_pos (show (0 : ℝ) < 4 by norm_num) hn0).ne' hq0.ne',
    Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num) hn0.ne']
  nlinarith

open DirichletCharacter in
/- English proof (translation)
Establish `hA : A.conductor ∣ (A * B).conductor`. Establish `h1 : A.conductor ∣ ((A * B).conductor).lcm (B⁻¹).conductor`. Use `conductor_mul_dvd_lcm_conductor (A * B) B⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_right]`. Then use the resulting hypothesis. Rewrite `h1` using `[conductor_inv]`.

Establish `h2 : A.conductor ∣ (A * B).conductor * B.conductor` using `h1.trans (Nat.lcm_dvd_mul _ _)`. Conclude with `h.dvd_of_dvd_mul_right h2`. Establish `hB : B.conductor ∣ (A * B).conductor`. Establish `h1 : B.conductor ∣ ((A * B).conductor).lcm (A⁻¹).conductor`. Use `conductor_mul_dvd_lcm_conductor (A * B) A⁻¹` as an intermediate fact.

Rewrite `this` using `[mul_comm A B, mul_inv_cancel_right, mul_comm B A]`. Then use the resulting hypothesis. Rewrite `h1` using `[conductor_inv]`. Establish `h2 : B.conductor ∣ (A * B).conductor * A.conductor` using `h1.trans (Nat.lcm_dvd_mul _ _)`. Conclude with `h.symm.dvd_of_dvd_mul_right h2`. Conclude with `h.mul_dvd_of_dvd_of_dvd hA hB`.
-/
private lemma cond_mul_coprime {n : ℕ} [NeZero n] (A B : DirichletCharacter ℂ n)
    (h : A.conductor.Coprime B.conductor) : A.conductor * B.conductor ∣ (A * B).conductor := by
  have hA : A.conductor ∣ (A * B).conductor := by
    have h1 : A.conductor ∣ ((A * B).conductor).lcm (B⁻¹).conductor := by
      have := conductor_mul_dvd_lcm_conductor (A * B) B⁻¹
      rwa [mul_inv_cancel_right] at this
    rw [conductor_inv] at h1
    have h2 : A.conductor ∣ (A * B).conductor * B.conductor := h1.trans (Nat.lcm_dvd_mul _ _)
    exact h.dvd_of_dvd_mul_right h2
  have hB : B.conductor ∣ (A * B).conductor := by
    have h1 : B.conductor ∣ ((A * B).conductor).lcm (A⁻¹).conductor := by
      have := conductor_mul_dvd_lcm_conductor (A * B) A⁻¹
      rwa [mul_comm A B, mul_inv_cancel_right, mul_comm B A] at this
    rw [conductor_inv] at h1
    have h2 : B.conductor ∣ (A * B).conductor * A.conductor := h1.trans (Nat.lcm_dvd_mul _ _)
    exact h.symm.dvd_of_dvd_mul_right h2
  exact h.mul_dvd_of_dvd_of_dvd hA hB

/- English proof (translation)
Introduce `h`. Take `⟨a, ha⟩` from `quadraticChar_exists_neg_one (F := ZMod q) (by rwa [ZMod.ringChar_zmod_n])`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at ha`.

Establish `h2` using `congrArg (fun χ : DirichletCharacter ℂ q => χ a) h`. Apply the tactic sequence `simp [qc, MulChar.ringHomComp_apply, ha, MulChar.one_apply (Ne.isUnit ha0)] at h2 <;>`. Evaluate the numerical expressions using `at h2`.
-/
private lemma qc_ne_one (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) : qc q ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod q) (by rwa [ZMod.ringChar_zmod_n])
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have h2 := congrArg (fun χ : DirichletCharacter ℂ q => χ a) h
  simp [qc, MulChar.ringHomComp_apply, ha, MulChar.one_apply (Ne.isUnit ha0)] at h2 <;>
    norm_num at h2

/- English proof (translation)
Establish `hp : q.Prime` using `Fact.out`. Use `haveI : NeZero q := ⟨hp.ne_zero⟩`. Break down `hp.eq_one_or_self_of_dvd _ (DirichletCharacter.conductor_dvd_level (qc q)) with h | h` into its components or cases. Conclude with `absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h) (qc_ne_one q hq)`. Conclude with `h`.
-/
private lemma qc_prim (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) : (qc q).IsPrimitive := by
  have hp : q.Prime := Fact.out
  haveI : NeZero q := ⟨hp.ne_zero⟩
  rcases hp.eq_one_or_self_of_dvd _ (DirichletCharacter.conductor_dvd_level (qc q)) with h | h
  · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h) (qc_ne_one q hq)
  · exact h

/- English proof (translation)
Unfold `qc`. Conclude with `((quadraticChar_isQuadratic (F := ZMod q)).comp (Int.castRingHom ℂ)).sq_eq_one`.
-/
private lemma qc_sq (q : ℕ) [Fact q.Prime] : qc q ^ 2 = 1 := by
  unfold qc
  exact ((quadraticChar_isQuadratic (F := ZMod q)).comp (Int.castRingHom ℂ)).sq_eq_one

/- English proof (translation)
Unfold `chi8`. Conclude with `(ZMod.isQuadratic_χ₈.comp (Int.castRingHom ℂ)).sq_eq_one`.
-/
private lemma chi_eight_sq : chi8 ^ 2 = 1 := by
  unfold chi8
  exact (ZMod.isQuadratic_χ₈.comp (Int.castRingHom ℂ)).sq_eq_one

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `h8 : chi8.conductor ∣ 2 ^ 3`. Simplify using `using DirichletCharacter.conductor_dvd_level chi8`. Take `⟨i, hi, hci⟩` from `(Nat.dvd_prime_pow Nat.prime_two).1 h8`. Establish `hi2 : i ≤ 2`.

Assume the negation of the conclusion as `h`. Establish `h3 : i = 3` using `by omega`. Conclude with `hne (by show chi8.conductor = 8; rw [hci, h3]; norm_num)`. Establish `h4 : chi8.conductor ∣ 4`. Rewrite using `[hci, show (4 : ℕ) = 2 ^ 2 by norm_num]`.

Conclude with `Nat.pow_dvd_pow 2 hi2`. Take `⟨hd, χ₀, hχ⟩` from `DirichletCharacter.factorsThrough_conductor chi8`. Establish `h48 : (4 : ℕ) ∣ 8` using `by norm_num`. Establish `hχ' : chi8 = DirichletCharacter.changeLevel h48 (DirichletCharacter.changeLevel h4 χ₀)`. Rewrite using `[← DirichletCharacter.changeLevel_trans]`.

Conclude with `hχ`. Establish `e : ∀ u : (ZMod 8)ˣ, chi8 u = (DirichletCharacter.changeLevel h4 χ₀) (ZMod.cast (u : ZMod 8))`. Introduce `u`. Conclude with `(congrArg (fun ψ : DirichletCharacter ℂ 8 => ψ u) hχ').trans (DirichletCharacter.changeLevel_eq_cast_of_dvd _ h48 u)`. Establish `h3 : Nat.Coprime 3 8` using `by norm_num`.

Establish `h7 : Nat.Coprime 7 8` using `by norm_num`. Establish `e3` using `e (ZMod.unitOfCoprime 3 h3)`. Establish `e7` using `e (ZMod.unitOfCoprime 7 h7)`. Rewrite `e3`, `e7` using `[ZMod.coe_unitOfCoprime]`. Establish `hc : (ZMod.cast ((3 : ℕ) : ZMod 8) : ZMod 4) = ZMod.cast ((7 : ℕ) : ZMod 8)`.

Evaluate the decidable proposition. Rewrite `e3` using `[hc, ← e7]`. Establish `v3 : ZMod.χ₈ ((3 : ℕ) : ZMod 8) = -1` using `by decide`. Establish `v7 : ZMod.χ₈ ((7 : ℕ) : ZMod 8) = 1` using `by decide`. Simplify using `only [chi8, MulChar.ringHomComp_apply, v3, v7] at e3`.

Evaluate the numerical expressions using `at e3`.
-/
private lemma chi_eight_primitive : chi8.IsPrimitive := by
  by_contra hne
  have h8 : chi8.conductor ∣ 2 ^ 3 := by
    simpa using DirichletCharacter.conductor_dvd_level chi8
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h8
  have hi2 : i ≤ 2 := by
    by_contra h
    have h3 : i = 3 := by omega
    exact hne (by show chi8.conductor = 8; rw [hci, h3]; norm_num)
  have h4 : chi8.conductor ∣ 4 := by
    rw [hci, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.pow_dvd_pow 2 hi2
  obtain ⟨hd, χ₀, hχ⟩ := DirichletCharacter.factorsThrough_conductor chi8
  have h48 : (4 : ℕ) ∣ 8 := by norm_num
  have hχ' : chi8 = DirichletCharacter.changeLevel h48 (DirichletCharacter.changeLevel h4 χ₀) := by
    rw [← DirichletCharacter.changeLevel_trans]
    exact hχ
  have e : ∀ u : (ZMod 8)ˣ, chi8 u =
      (DirichletCharacter.changeLevel h4 χ₀) (ZMod.cast (u : ZMod 8)) := by
    intro u
    exact (congrArg (fun ψ : DirichletCharacter ℂ 8 => ψ u) hχ').trans
      (DirichletCharacter.changeLevel_eq_cast_of_dvd _ h48 u)
  have h3 : Nat.Coprime 3 8 := by norm_num
  have h7 : Nat.Coprime 7 8 := by norm_num
  have e3 := e (ZMod.unitOfCoprime 3 h3)
  have e7 := e (ZMod.unitOfCoprime 7 h7)
  rw [ZMod.coe_unitOfCoprime] at e3 e7
  have hc : (ZMod.cast ((3 : ℕ) : ZMod 8) : ZMod 4) = ZMod.cast ((7 : ℕ) : ZMod 8) := by
    decide
  rw [hc, ← e7] at e3
  have v3 : ZMod.χ₈ ((3 : ℕ) : ZMod 8) = -1 := by decide
  have v7 : ZMod.χ₈ ((7 : ℕ) : ZMod 8) = 1 := by decide
  simp only [chi8, MulChar.ringHomComp_apply, v3, v7] at e3
  norm_num at e3

/- English proof (translation)
Use `⟨⟨chi_eight_primitive, chi_eight_sq⟩, ?_⟩` and prove the remaining obligations. Introduce `t θ q hF hθ hq2 hc`. Establish `hp : q.Prime` using `Fact.out`. Establish `ht : t ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hp.one_lt.ne' (by simpa using hc)`. Use `haveI : NeZero t := ⟨ht⟩`. Use `haveI : NeZero q := ⟨hp.ne_zero⟩`. Use `haveI : NeZero (t * q) := ⟨mul_ne_zero ht hp.ne_zero⟩`. Establish `hA : (DirichletCharacter.changeLevel (Dvd.intro q rfl) θ).conductor = t`.

Rewrite using `[DirichletCharacter.conductor_changeLevel]`. Conclude with `hθ`. Establish `hB : (DirichletCharacter.changeLevel (Dvd.intro_left t rfl) (qc q)).conductor = q`. Rewrite using `[DirichletCharacter.conductor_changeLevel]`. Conclude with `qc_prim q hq2`.

Establish `hcop : (DirichletCharacter.changeLevel (Dvd.intro q rfl) θ).conductor.Coprime (DirichletCharacter.changeLevel (Dvd.intro_left t rfl) (qc q)).conductor`. Rewrite using `[hA, hB]`. Conclude with `hc.symm`. Establish `hdvd` using `cond_mul_coprime _ _ hcop`. Rewrite `hdvd` using `[hA, hB]`.

Establish `hprim : (tw θ q).conductor = t * q` using `Nat.dvd_antisymm (DirichletCharacter.conductor_dvd_level _) hdvd`. Use `⟨hprim, ?_, ?_⟩` and prove the remaining obligations. Introduce `h1`. Establish `h1'` using `DirichletCharacter.eq_one_iff_conductor_eq_one.mp h1`. Rewrite `h1'` using `[hprim]`.

Establish `h2q` using `hp.two_le`. Establish `ht1 : 1 ≤ t` using `Nat.pos_of_ne_zero ht`. Use the polynomial consequences of the given equalities and inequalities. Introduce `hθ2`. Unfold `tw`.

Rewrite using `[mul_pow, ← map_pow, ← map_pow, hθ2, qc_sq, map_one, map_one, one_mul]`.
-/
private theorem twist_is_primitive : TwPrimitive := by
  refine ⟨⟨chi_eight_primitive, chi_eight_sq⟩, ?_⟩
  intro t θ q hF hθ hq2 hc
  have hp : q.Prime := Fact.out
  have ht : t ≠ 0 := by
    rintro rfl
    exact hp.one_lt.ne' (by simpa using hc)
  haveI : NeZero t := ⟨ht⟩
  haveI : NeZero q := ⟨hp.ne_zero⟩
  haveI : NeZero (t * q) := ⟨mul_ne_zero ht hp.ne_zero⟩
  have hA : (DirichletCharacter.changeLevel (Dvd.intro q rfl) θ).conductor = t := by
    rw [DirichletCharacter.conductor_changeLevel]
    exact hθ
  have hB : (DirichletCharacter.changeLevel (Dvd.intro_left t rfl) (qc q)).conductor = q := by
    rw [DirichletCharacter.conductor_changeLevel]
    exact qc_prim q hq2
  have hcop : (DirichletCharacter.changeLevel (Dvd.intro q rfl) θ).conductor.Coprime
      (DirichletCharacter.changeLevel (Dvd.intro_left t rfl) (qc q)).conductor := by
    rw [hA, hB]
    exact hc.symm
  have hdvd := cond_mul_coprime _ _ hcop
  rw [hA, hB] at hdvd
  have hprim : (tw θ q).conductor = t * q :=
    Nat.dvd_antisymm (DirichletCharacter.conductor_dvd_level _) hdvd
  refine ⟨hprim, ?_, ?_⟩
  · intro h1
    have h1' := DirichletCharacter.eq_one_iff_conductor_eq_one.mp h1
    rw [hprim] at h1'
    have h2q := hp.two_le
    have ht1 : 1 ≤ t := Nat.pos_of_ne_zero ht
    nlinarith
  · intro hθ2
    unfold tw
    rw [mul_pow, ← map_pow, ← map_pow, hθ2, qc_sq, map_one, map_one, one_mul]

open Finset ArithmeticFunction in
private noncomputable def SS {t : ℕ} (θ : DirichletCharacter ℂ t) (x : ℝ) (q : ℕ) : ℝ :=
  ‖∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, ((cN x n : ℝ) : ℂ) * θ (n : ZMod t) * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖

open Classical in
private noncomputable def badSet {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (P : Finset ℕ) :
    Finset ℕ :=
  P.filter (fun q => ∃ h : Fact q.Prime, ¬ ZeroFreeBox Q (@tw t θ q h))

open Classical in
/- English proof (translation)
Rewrite using `[badSet, Finset.mem_filter]`.
-/
private lemma mem_badSet {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (P : Finset ℕ) (q : ℕ) :
    q ∈ badSet θ Q P ↔ q ∈ P ∧ ∃ h : Fact q.Prime, ¬ ZeroFreeBox Q (@tw t θ q h) := by
  rw [badSet, Finset.mem_filter]

/- English proof (translation)
Rewrite `h` using `[PPset, Finset.mem_filter, Finset.mem_Icc]`. Take `⟨⟨_, hq⟩, hp, hm, hlt⟩` from `h`. Conclude with `⟨hp, hm, hlt, (Nat.le_floor_iff hX).1 hq⟩`.
-/
private lemma mem_PP {m a q : ℕ} {X : ℝ} (hX : 0 ≤ X) (h : q ∈ PPset m a X) :
    q.Prime ∧ q % m = a % m ∧ X ^ (1 / 2 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ X := by
  rw [PPset, Finset.mem_filter, Finset.mem_Icc] at h
  obtain ⟨⟨_, hq⟩, hp, hm, hlt⟩ := h
  exact ⟨hp, hm, hlt, (Nat.le_floor_iff hX).1 hq⟩

/- English proof (translation)
Use `hBC t θ Q (badSet θ Q P) h1 h2 ?_` and prove the remaining obligations. Introduce `q hq`. Take `⟨hqP, hF, hz⟩` from `(mem_badSet θ Q P q).1 hq`. Take `⟨h4, hc, hQ⟩` from `hP q hqP`. Conclude with `⟨hF, h4, hc, hQ, hz⟩`.
-/
private lemma badCard {C : ℝ} (hBC : BoxCountHyp C) {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ)
    (P : Finset ℕ) (h1 : θ.IsPrimitive) (h2 : θ ^ 2 = 1)
    (hP : ∀ q ∈ P, q % 4 = 3 ∧ q.Coprime t ∧ ((t * q : ℕ) : ℝ) ≤ Q) :
    ((badSet θ Q P).card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ) := by
  refine hBC t θ Q (badSet θ Q P) h1 h2 ?_
  intro q hq
  obtain ⟨hqP, hF, hz⟩ := (mem_badSet θ Q P q).1 hq
  obtain ⟨h4, hc, hQ⟩ := hP q hqP
  exact ⟨hF, h4, hc, hQ, hz⟩

/- English proof (translation)
Establish `hT : TwPrimitive` using `twist_is_primitive`. Unfold `TwPrimitive at hT`. Take `⟨hp, hne, hsq⟩` from `hT.2 t θ q h1 hq2 hc`. Use `⟨?_, hne⟩` and prove the remaining obligations. Unfold `GoodFor`.

Use `⟨hp, hsq h2, hQ, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hz`. Conclude with `hb ((mem_badSet θ Q P q).2 ⟨hqP, hF, hz⟩)`.
-/
private lemma goodOf {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (P : Finset ℕ) (q : ℕ)
    [hF : Fact q.Prime] (h1 : θ.IsPrimitive) (h2 : θ ^ 2 = 1) (hq2 : q ≠ 2) (hc : q.Coprime t)
    (hQ : ((t * q : ℕ) : ℝ) ≤ Q) (hqP : q ∈ P) (hb : q ∉ badSet θ Q P) :
    GoodFor Q (tw θ q) ∧ tw θ q ≠ 1 := by
  have hT : TwPrimitive := twist_is_primitive
  unfold TwPrimitive at hT
  obtain ⟨hp, hne, hsq⟩ := hT.2 t θ q h1 hq2 hc
  refine ⟨?_, hne⟩
  unfold GoodFor
  refine ⟨hp, hsq h2, hQ, ?_⟩
  by_contra hz
  exact hb ((mem_badSet θ Q P q).2 ⟨hqP, hF, hz⟩)

/- English proof (translation)
Take `⟨t1, t2⟩` from `hBT x Q (t * q) (tw θ q) hx2 hw1 hw2 hg.2 hg.1`. Use `⟨?_, t2⟩` and prove the remaining obligations. Establish `hxz : x ≤ x ^ 400` using `le_self_pow₀ hx1 (by norm_num)`. Rewrite using `[finite_splitting_of_group (t * q) (tw θ q) x (x ^ 400) (by linarith) hxz]`. Establish `hSz : ‖Sz (tw θ q) x (x ^ 400)‖ = SS θ x q`.

Unfold `Sz SS`. Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n _`. Rewrite using `[twist_evaluation_formula t θ q n, mul_assoc]`.

Combine the equalities or inequalities in the displayed calculation.
-/
private lemma gBound {ε C x₂ x Q : ℝ} (hBT : BoxTailHyp ε C x₂) (hx2 : x₂ ≤ x) (hx1 : 1 ≤ x)
    (hw1 : x ^ (ε / 6) ≤ Real.log Q) (hw2 : Real.log Q ≤ x ^ (ε / 4))
    (hlast : x ^ (1 / 2 + ε) / 2 + x ^ ε ≤ x ^ (1 / 2 + ε))
    {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime]
    (hg : GoodFor Q (tw θ q) ∧ tw θ q ≠ 1) (hS : SS θ x q ≤ x ^ (1 / 2 + ε) / 2) :
    ‖Gchi (tw θ q) x‖ ≤ x ^ (1 / 2 + ε) ∧ ‖logDerivLAtOne (tw θ q)‖ ≤ C * Real.log x := by
  obtain ⟨t1, t2⟩ := hBT x Q (t * q) (tw θ q) hx2 hw1 hw2 hg.2 hg.1
  refine ⟨?_, t2⟩
  have hxz : x ≤ x ^ 400 := le_self_pow₀ hx1 (by norm_num)
  rw [finite_splitting_of_group (t * q) (tw θ q) x (x ^ 400) (by linarith) hxz]
  have hSz : ‖Sz (tw θ q) x (x ^ 400)‖ = SS θ x q := by
    unfold Sz SS
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [twist_evaluation_formula t θ q n, mul_assoc]
  calc ‖- Sz (tw θ q) x (x ^ 400) - (x : ℂ) * tailL (tw θ q) (x ^ 400)‖
      ≤ ‖- Sz (tw θ q) x (x ^ 400)‖ + ‖(x : ℂ) * tailL (tw θ q) (x ^ 400)‖ := norm_sub_le _ _
    _ ≤ x ^ (1 / 2 + ε) := by rw [norm_neg, hSz]; linarith

/- English proof (translation)
The claim follows from `DirichletCharacter.norm_le_one θ _`.
-/
private lemma kappa_norm {t : ℕ} (θ : DirichletCharacter ℂ t) (n : ℕ) : ‖θ (n : ZMod t)‖ ≤ 1 := DirichletCharacter.norm_le_one θ _

/- English proof (translation)
Rewrite using `[Nat.cast_mul, map_mul]`.
-/
private lemma kappa_mul {t : ℕ} (θ : DirichletCharacter ℂ t) (a b : ℕ) :
    θ ((a * b : ℕ) : ZMod t) = θ (a : ZMod t) * θ (b : ZMod t) := by
  rw [Nat.cast_mul, map_mul]

/- English proof (translation)
Use `show one1.conductor = 1`. Conclude with `Nat.dvd_one.mp (DirichletCharacter.conductor_dvd_level _)`.
-/
private lemma trivial_character_primitive : one1.IsPrimitive := by
  show one1.conductor = 1
  exact Nat.dvd_one.mp (DirichletCharacter.conductor_dvd_level _)
/- English proof (translation)
Simplify using `[one1]`.
-/
private lemma trivial_character_sq : one1 ^ 2 = 1 := by
  simp [one1]

/- English proof (translation)
Introduce `ε C₂ C₂' x₂ C₄ x₄ hε hε1 hC₂ hC₄ hBC hBT hMS`. Take `⟨xa, ha⟩` from `numerical_bound_unit_modulus ε C₂ hε hε1 hC₂`. Take `⟨xb, hb⟩` from `numerical_bound_unit_modulus ε C₄ hε hε1 hC₄`. Take `⟨xc, hc⟩` from `numerical_zero_density_bound ε C₂ hε hε1 hC₂`. Use `⟨max (max (max x₂ x₄) (max xa xb)) (max xc 1), fun x hx => ?_⟩` and prove the remaining obligations.

Establish `hx2 : x₂ ≤ x` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx`. Establish `hx4 : x₄ ≤ x` using `le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx`. Establish `hxa : xa ≤ x` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx`. Establish `hxb : xb ≤ x` using `le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx`. Establish `hxc : xc ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx`.

Establish `hx1 : 1 ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx`. Establish `hx0 : 0 < x` using `by linarith`. Take `⟨a1, a2, a3, -, a5, a6, a7, -, a9, a10⟩` from `ha x hxa`. Take `⟨-, -, -, -, -, -, -, b8, -, -⟩` from `hb x hxb`. Take `⟨c1, c2, -, c4, c5, c6, c7⟩` from `hc x hxc`.

Use `set y := x ^ (ε / 5) with hy`. Use `set t := x ^ (1 / 2 + ε) / 2 with ht`. Use `set V := C₄ * x * Real.log x with hV`. Establish `htpos : 0 < t` using `by have := Real.rpow_pos_of_pos hx0 (1 / 2 + ε); positivity`. Establish `hr : V / t ^ 2 ≤ 1 / 8` using `le_trans b8 a9`.

Establish `hX1` using `exp_scale_pos ε x`. Establish `hX2` using `double_exp_scale_pos ε x`. Establish `hX1one : 1 ≤ X1 ε x` using `Real.one_le_exp (Real.rpow_nonneg hx0.le _)`. Take `⟨hP1, hM1⟩` from `hMS x (X1 ε x) 8 3 (fun n => one1 (n : ZMod 1)) hx4 (by norm_num) (by`. Introduce `p hp hp8`.

Use `left`. Establish `: p ∣ 2 ^ 3` using `by simpa using hp8`. Establish `h2` using `(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this)`. Substitute `h2` using the available equality. Conclude with `a2)` after adjusting the coercions.

Use the proof step `(by decide) (by norm_num) (by exact_mod_cast a3) a5 (kappa_norm one1) (kappa_mul one1)`. Use `set P1 := PPset 8 3 (X1 ε x) with hP1def`. Establish `hP1mem : ∀ q ∈ P1, q.Prime ∧ q % 8 = 3 ∧ X1 ε x ^ (1 / 2 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ X1 ε x`. Introduce `q hq`. Take `⟨u1, u2, u3, u4⟩` from `mem_PP hX1.le hq`.

Conclude with `⟨u1, by omega, u3, u4⟩`. Establish `hodd8 : ∀ q : ℕ, q % 2 = 1 → q.Coprime 8`. Introduce `q hq`. Rewrite using `[show (8 : ℕ) = 2 ^ 3 by norm_num]`. Apply `Nat.Coprime.pow_right` to reduce the goal to its premises.

Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]`. Use linear arithmetic over natural numbers and integers. Establish `hB1a` using `badCard hBC one1 (8 * X1 ε x) P1 trivial_character_primitive trivial_character_sq (by`. Introduce `q hq`. Take `⟨u1, u2, u3, u4⟩` from `hP1mem q hq`.

Use `⟨by omega, Nat.coprime_one_right q, ?_⟩` and prove the remaining obligations. Use `push_cast`. Use the proof step `linarith)`. Establish `hB1b` using `badCard hBC chi8 (8 * X1 ε x) P1 twist_is_primitive.1.1 twist_is_primitive.1.2 (by`. Introduce `q hq`.

Take `⟨u1, u2, u3, u4⟩` from `hP1mem q hq`. Use `⟨by omega, hodd8 q (by omega), ?_⟩` and prove the remaining obligations. Use `push_cast`. Use the proof step `linarith)`. Establish `hp1pos : (0 : ℝ) < (P1.card : ℝ)` using `lt_of_lt_of_le (Real.rpow_pos_of_pos hX1 _) hP1`.

Take `⟨q₁, hq₁P, hq₁B, hq₁S⟩` from `markov_discard_bound P1 (badSet one1 (8 * X1 ε x) P1 ∪ badSet chi8 (8 * X1 ε x) P1) 1 (fun _ q => SS one1 x q) V t htpos (fun _ => hM1) (by`. Establish `h1 : (((badSet one1 (8 * X1 ε x) P1 ∪ badSet chi8 (8 * X1 ε x) P1).card : ℕ) : ℝ) ≤ ((badSet one1 (8 * X1 ε x) P1).card : ℝ) + ((badSet chi8 (8 * X1 ε x) P1).card : ℝ)`. Conclude with `Finset.card_union_le _ _` after adjusting the coercions. Establish `h2` using `mul_le_mul_of_nonneg_right hr hp1pos.le`. Use `push_cast`.

Use the proof step `linarith)`. Rewrite `hq₁B` using `[Finset.mem_union, not_or]`. Take `⟨q1p, q18, q1lo, q1hi⟩` from `hP1mem q₁ hq₁P`. Establish `hF1 : Fact q₁.Prime` using `⟨q1p⟩`. Establish `q1ne2 : q₁ ≠ 2` using `by omega`.

Establish `q1S : SS one1 x q₁ ≤ t` using `le_trans (le_abs_self _) (hq₁S 0)`. Establish `g1` using `goodOf one1 (8 * X1 ε x) P1 q₁ trivial_character_primitive trivial_character_sq q1ne2 (Nat.coprime_one_right _) (by push_cast; linarith) hq₁P hq₁B.1`. Establish `g2` using `goodOf chi8 (8 * X1 ε x) P1 q₁ twist_is_primitive.1.1 twist_is_primitive.1.2 q1ne2 (hodd8 q₁ (by omega)) (by push_cast; linarith) hq₁P hq₁B.2`. Establish `hy0 : 0 ≤ y` using `by linarith`. Take `⟨a₀, e1, e2, e3, e4, e5, e6, e7⟩` from `class_admissible y (x ^ 400) q₁ a2 q1p q18 (lt_trans a1 q1lo)`.

Use `set M := oddM y q₁ with hMdef`. Establish `hMpos : 0 < M` using `Nat.pos_of_ne_zero (by`. Introduce `h`. Rewrite `e2` using `[h, zero_dvd_iff]`. Use the proof step `omega)`.

Establish `hm0 : (1 / 4) * Real.log x ^ 2 * Real.log ((16 * M : ℕ) : ℝ) ≤ Real.log (X2 ε x)`. Apply `c1` to reduce the goal to its premises. Conclude with `Nat.mul_pos (by norm_num) hMpos` after adjusting the coercions. Use `primorial_upper_bound y q₁ hy0 q1hi` as an intermediate fact. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hMS2 : ∀ {s : ℕ} (θ : DirichletCharacter ℂ s), X2 ε x ^ (9 / 10 : ℝ) ≤ ((PPset (16 * M) a₀ (X2 ε x)).card : ℝ) ∧ (∑ q ∈ PPset (16 * M) a₀ (X2 ε x), SS θ x q ^ 2) ≤ V * ((PPset (16 * M) a₀ (X2 ε x)).card : ℝ)` using `fun {s} θ => hMS x (X2 ε x) (16 * M) a₀ (fun n => θ (n : ZMod s)) hx4 e5 e6 e3 e4 hm0 c2 (kappa_norm θ) (kappa_mul θ)`. Use `set P2 := PPset (16 * M) a₀ (X2 ε x) with hP2def`. Use `set Q := 8 * X1 ε x * X2 ε x with hQ`. Establish `hP2mem : ∀ d ∈ P2, d.Prime ∧ d % 16 = 7 ∧ M ∣ d + 1 ∧ X2 ε x ^ (1 / 2 : ℝ) < (d : ℝ) ∧ (d : ℝ) ≤ X2 ε x ∧ d.Coprime q₁ ∧ (d : ℝ) ≤ X1 ε x * X2 ε x ∧ (q₁ : ℝ) * d ≤ X1 ε x * X2 ε x`.

Introduce `d hd`. Take `⟨u1, u2, u3, u4⟩` from `mem_PP hX2.le hd`. Take `⟨v1, v2⟩` from `e7 d u2`. Use `⟨u1, v1, v2, u3, u4, ?_, by nlinarith, mul_le_mul q1hi u4 (Nat.cast_nonneg _) hX1.le⟩` and prove the remaining obligations. Rewrite using `[Nat.coprime_primes u1 q1p]`.

Introduce and unpack `rfl`. Establish `h1 : d ∣ d + 1` using `(Dvd.intro _ rfl : d ∣ M).trans v2`. Establish `h2 : d ∣ 1` using `(Nat.dvd_add_right (dvd_refl d)).1 h1`. Conclude with `u1.one_lt.ne' (Nat.dvd_one.1 h2)`. Establish `hXX : 0 < X1 ε x * X2 ε x` using `mul_pos hX1 hX2`.

Establish `hQeq : Q = 8 * (X1 ε x * X2 ε x)` using `by rw [hQ]; ring`. Establish `side1 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime 1 ∧ ((1 * d : ℕ) : ℝ) ≤ Q`. Introduce `d hd`. Take `⟨u1, u2, u3, u4, u5, u6, u7, u8⟩` from `hP2mem d hd`. Conclude with `⟨by omega, Nat.coprime_one_right d, by push_cast; rw [hQeq]; linarith⟩`.

Establish `side2 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime 8 ∧ ((8 * d : ℕ) : ℝ) ≤ Q`. Introduce `d hd`. Take `⟨u1, u2, u3, u4, u5, u6, u7, u8⟩` from `hP2mem d hd`. Conclude with `⟨by omega, hodd8 d (by omega), by push_cast; rw [hQeq]; linarith⟩`. Establish `side3 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime (1 * q₁) ∧ ((1 * q₁ * d : ℕ) : ℝ) ≤ Q`.

Introduce `d hd`. Take `⟨u1, u2, u3, u4, u5, u6, u7, u8⟩` from `hP2mem d hd`. Conclude with `⟨by omega, by rwa [one_mul], by push_cast; rw [hQeq]; linarith⟩`. Establish `side4 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime (8 * q₁) ∧ ((8 * q₁ * d : ℕ) : ℝ) ≤ Q`. Introduce `d hd`.

Take `⟨u1, u2, u3, u4, u5, u6, u7, u8⟩` from `hP2mem d hd`. Conclude with `⟨by omega, Nat.Coprime.mul_right (hodd8 d (by omega)) u6, by push_cast; rw [hQeq]; linarith⟩`. Establish `k1` using `badCard hBC one1 Q P2 trivial_character_primitive trivial_character_sq side1`. Establish `k2` using `badCard hBC chi8 Q P2 twist_is_primitive.1.1 twist_is_primitive.1.2 side2`. Establish `k3` using `badCard hBC (tw one1 q₁) Q P2 g1.1.1 g1.1.2.1 side3`.

Establish `k4` using `badCard hBC (tw chi8 q₁) Q P2 g2.1.1 g2.1.2.1 side4`. Establish `hP2` using `(hMS2 one1).1`. Establish `hp2pos : (0 : ℝ) < (P2.card : ℝ)` using `lt_of_lt_of_le (Real.rpow_pos_of_pos hX2 _) hP2`. Take `⟨d, hdP, hdB, hdS⟩` from `markov_discard_bound P2 ((badSet one1 Q P2 ∪ badSet chi8 Q P2) ∪ (badSet (tw one1 q₁) Q P2 ∪ badSet (tw chi8 q₁) Q P2)) 2 (fun j q => if j = 0 then SS one1 x q else SS (tw one1 q₁) x q) V t htpos (by`. Introduce `j`.

Distinguish the cases in `hj : j = 0`. Simplify using `only [hj, if_true]`. Conclude with `(hMS2 one1).2`. Simplify using `only [hj, if_false]`. Conclude with `(hMS2 (tw one1 q₁)).2)`.

Use the proof step `(by`. Establish `h1 : ((((badSet one1 Q P2 ∪ badSet chi8 Q P2) ∪ (badSet (tw one1 q₁) Q P2 ∪ badSet (tw chi8 q₁) Q P2)).card : ℕ) : ℝ) ≤ (((badSet one1 Q P2).card : ℝ) + ((badSet chi8 Q P2).card : ℝ)) + (((badSet (tw one1 q₁) Q P2).card : ℝ) + ((badSet (tw chi8 q₁) Q P2).card : ℝ))`. Conclude with `(Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _))` after adjusting the coercions. Establish `h2` using `mul_le_mul_of_nonneg_right hr hp2pos.le`. Use `push_cast`.

Use the proof step `linarith)`. Simplify using `only [Finset.mem_union, not_or] at hdB`. Take `⟨⟨nb1, nb2⟩, nb3, nb4⟩` from `hdB`. Take `⟨dp, d16, dM, dlo, dhi, -, -, -⟩` from `hP2mem d hdP`. Establish `hF2 : Fact d.Prime` using `⟨dp⟩`.

Establish `dne2 : d ≠ 2` using `by omega`. Establish `dS0 : SS one1 x d ≤ t` using `le_trans (le_abs_self _) (by simpa using hdS 0)`. Establish `dS1 : SS (tw one1 q₁) x d ≤ t` using `le_trans (le_abs_self _) (by simpa using hdS 1)`. Establish `g3` using `goodOf one1 Q P2 d trivial_character_primitive trivial_character_sq dne2 (side1 d hdP).2.1 (side1 d hdP).2.2 hdP nb1`. Establish `g4` using `goodOf chi8 Q P2 d twist_is_primitive.1.1 twist_is_primitive.1.2 dne2 (side2 d hdP).2.1 (side2 d hdP).2.2 hdP nb2`.

Establish `g5` using `goodOf (tw one1 q₁) Q P2 d g1.1.1 g1.1.2.1 dne2 (side3 d hdP).2.1 (side3 d hdP).2.2 hdP nb3`. Establish `g6` using `goodOf (tw chi8 q₁) Q P2 d g2.1.1 g2.1.2.1 dne2 (side4 d hdP).2.1 (side4 d hdP).2.2 hdP nb4`. Take `⟨sp1, sp2⟩` from `class_splits y q₁ d q1p d16 dM`. Conclude with `⟨q₁, d, hF1, hF2, q18, d16, q1lo, q1hi, dlo, dhi, sp1, sp2, g1.1, g2.1, g3.1, g4.1, g5.1, g6.1, gBound hBT hx2 hx1 a6 a7 c7 one1 q₁ g1 q1S, gBound hBT hx2 hx1 c4 c5 c7 one1 d g3 dS0, gBound hBT hx2 hx1 c4 c5 c7 (tw one1 q₁) d g5 dS1⟩`.
-/
theorem zero_density_of_hypothesis : PrimePairOfBoxAndMeanSquareHypotheses := by
  intro ε C₂ C₂' x₂ C₄ x₄ hε hε1 hC₂ hC₄ hBC hBT hMS
  obtain ⟨xa, ha⟩ := numerical_bound_unit_modulus ε C₂ hε hε1 hC₂
  obtain ⟨xb, hb⟩ := numerical_bound_unit_modulus ε C₄ hε hε1 hC₄
  obtain ⟨xc, hc⟩ := numerical_zero_density_bound ε C₂ hε hε1 hC₂
  refine ⟨max (max (max x₂ x₄) (max xa xb)) (max xc 1), fun x hx => ?_⟩
  have hx2 : x₂ ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hx4 : x₄ ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxa : xa ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hxb : xb ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hxc : xc ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 < x := by linarith
  obtain ⟨a1, a2, a3, -, a5, a6, a7, -, a9, a10⟩ := ha x hxa
  obtain ⟨-, -, -, -, -, -, -, b8, -, -⟩ := hb x hxb
  obtain ⟨c1, c2, -, c4, c5, c6, c7⟩ := hc x hxc
  set y := x ^ (ε / 5) with hy
  set t := x ^ (1 / 2 + ε) / 2 with ht
  set V := C₄ * x * Real.log x with hV
  have htpos : 0 < t := by have := Real.rpow_pos_of_pos hx0 (1 / 2 + ε); positivity
  have hr : V / t ^ 2 ≤ 1 / 8 := le_trans b8 a9
  have hX1 := exp_scale_pos ε x
  have hX2 := double_exp_scale_pos ε x
  have hX1one : 1 ≤ X1 ε x := Real.one_le_exp (Real.rpow_nonneg hx0.le _)

  obtain ⟨hP1, hM1⟩ := hMS x (X1 ε x) 8 3 (fun n => one1 (n : ZMod 1)) hx4 (by norm_num)
    (by
      intro p hp hp8
      left
      have : p ∣ 2 ^ 3 := by simpa using hp8
      have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this)
      subst h2; exact_mod_cast a2)
    (by decide) (by norm_num) (by exact_mod_cast a3) a5 (kappa_norm one1) (kappa_mul one1)
  set P1 := PPset 8 3 (X1 ε x) with hP1def
  have hP1mem : ∀ q ∈ P1, q.Prime ∧ q % 8 = 3 ∧ X1 ε x ^ (1 / 2 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ X1 ε x := by
    intro q hq
    obtain ⟨u1, u2, u3, u4⟩ := mem_PP hX1.le hq
    exact ⟨u1, by omega, u3, u4⟩
  have hodd8 : ∀ q : ℕ, q % 2 = 1 → q.Coprime 8 := by
    intro q hq
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  have hB1a := badCard hBC one1 (8 * X1 ε x) P1 trivial_character_primitive trivial_character_sq (by
    intro q hq
    obtain ⟨u1, u2, u3, u4⟩ := hP1mem q hq
    refine ⟨by omega, Nat.coprime_one_right q, ?_⟩
    push_cast; linarith)
  have hB1b := badCard hBC chi8 (8 * X1 ε x) P1 twist_is_primitive.1.1 twist_is_primitive.1.2 (by
    intro q hq
    obtain ⟨u1, u2, u3, u4⟩ := hP1mem q hq
    refine ⟨by omega, hodd8 q (by omega), ?_⟩
    push_cast; linarith)
  have hp1pos : (0 : ℝ) < (P1.card : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hX1 _) hP1
  obtain ⟨q₁, hq₁P, hq₁B, hq₁S⟩ := markov_discard_bound P1
    (badSet one1 (8 * X1 ε x) P1 ∪ badSet chi8 (8 * X1 ε x) P1) 1 (fun _ q => SS one1 x q) V t htpos
    (fun _ => hM1) (by
      have h1 : (((badSet one1 (8 * X1 ε x) P1 ∪ badSet chi8 (8 * X1 ε x) P1).card : ℕ) : ℝ) ≤
          ((badSet one1 (8 * X1 ε x) P1).card : ℝ) + ((badSet chi8 (8 * X1 ε x) P1).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
      have h2 := mul_le_mul_of_nonneg_right hr hp1pos.le
      push_cast
      linarith)
  rw [Finset.mem_union, not_or] at hq₁B
  obtain ⟨q1p, q18, q1lo, q1hi⟩ := hP1mem q₁ hq₁P
  have hF1 : Fact q₁.Prime := ⟨q1p⟩
  have q1ne2 : q₁ ≠ 2 := by omega
  have q1S : SS one1 x q₁ ≤ t := le_trans (le_abs_self _) (hq₁S 0)
  have g1 := goodOf one1 (8 * X1 ε x) P1 q₁ trivial_character_primitive trivial_character_sq q1ne2 (Nat.coprime_one_right _)
    (by push_cast; linarith) hq₁P hq₁B.1
  have g2 := goodOf chi8 (8 * X1 ε x) P1 q₁ twist_is_primitive.1.1 twist_is_primitive.1.2 q1ne2 (hodd8 q₁ (by omega))
    (by push_cast; linarith) hq₁P hq₁B.2

  have hy0 : 0 ≤ y := by linarith
  obtain ⟨a₀, e1, e2, e3, e4, e5, e6, e7⟩ := class_admissible y (x ^ 400) q₁ a2 q1p q18 (lt_trans a1 q1lo)
  set M := oddM y q₁ with hMdef
  have hMpos : 0 < M := Nat.pos_of_ne_zero (by
    intro h; rw [h, zero_dvd_iff] at e2; omega)
  have hm0 : (1 / 4) * Real.log x ^ 2 * Real.log ((16 * M : ℕ) : ℝ) ≤ Real.log (X2 ε x) := by
    apply c1
    · exact_mod_cast Nat.mul_pos (by norm_num) hMpos
    · have := primorial_upper_bound y q₁ hy0 q1hi
      push_cast
      linarith
  have hMS2 : ∀ {s : ℕ} (θ : DirichletCharacter ℂ s),
      X2 ε x ^ (9 / 10 : ℝ) ≤ ((PPset (16 * M) a₀ (X2 ε x)).card : ℝ) ∧
      (∑ q ∈ PPset (16 * M) a₀ (X2 ε x), SS θ x q ^ 2) ≤ V * ((PPset (16 * M) a₀ (X2 ε x)).card : ℝ) :=
    fun {s} θ => hMS x (X2 ε x) (16 * M) a₀ (fun n => θ (n : ZMod s)) hx4 e5 e6 e3 e4 hm0 c2
      (kappa_norm θ) (kappa_mul θ)
  set P2 := PPset (16 * M) a₀ (X2 ε x) with hP2def
  set Q := 8 * X1 ε x * X2 ε x with hQ
  have hP2mem : ∀ d ∈ P2, d.Prime ∧ d % 16 = 7 ∧ M ∣ d + 1 ∧ X2 ε x ^ (1 / 2 : ℝ) < (d : ℝ) ∧ (d : ℝ) ≤ X2 ε x ∧
      d.Coprime q₁ ∧ (d : ℝ) ≤ X1 ε x * X2 ε x ∧ (q₁ : ℝ) * d ≤ X1 ε x * X2 ε x := by
    intro d hd
    obtain ⟨u1, u2, u3, u4⟩ := mem_PP hX2.le hd
    obtain ⟨v1, v2⟩ := e7 d u2
    refine ⟨u1, v1, v2, u3, u4, ?_, by nlinarith, mul_le_mul q1hi u4 (Nat.cast_nonneg _) hX1.le⟩
    rw [Nat.coprime_primes u1 q1p]
    rintro rfl
    have h1 : d ∣ d + 1 := (Dvd.intro _ rfl : d ∣ M).trans v2
    have h2 : d ∣ 1 := (Nat.dvd_add_right (dvd_refl d)).1 h1
    exact u1.one_lt.ne' (Nat.dvd_one.1 h2)
  have hXX : 0 < X1 ε x * X2 ε x := mul_pos hX1 hX2
  have hQeq : Q = 8 * (X1 ε x * X2 ε x) := by rw [hQ]; ring
  have side1 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime 1 ∧ ((1 * d : ℕ) : ℝ) ≤ Q := by
    intro d hd
    obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := hP2mem d hd
    exact ⟨by omega, Nat.coprime_one_right d, by push_cast; rw [hQeq]; linarith⟩
  have side2 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime 8 ∧ ((8 * d : ℕ) : ℝ) ≤ Q := by
    intro d hd
    obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := hP2mem d hd
    exact ⟨by omega, hodd8 d (by omega), by push_cast; rw [hQeq]; linarith⟩
  have side3 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime (1 * q₁) ∧ ((1 * q₁ * d : ℕ) : ℝ) ≤ Q := by
    intro d hd
    obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := hP2mem d hd
    exact ⟨by omega, by rwa [one_mul], by push_cast; rw [hQeq]; linarith⟩
  have side4 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime (8 * q₁) ∧ ((8 * q₁ * d : ℕ) : ℝ) ≤ Q := by
    intro d hd
    obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := hP2mem d hd
    exact ⟨by omega, Nat.Coprime.mul_right (hodd8 d (by omega)) u6, by push_cast; rw [hQeq]; linarith⟩
  have k1 := badCard hBC one1 Q P2 trivial_character_primitive trivial_character_sq side1
  have k2 := badCard hBC chi8 Q P2 twist_is_primitive.1.1 twist_is_primitive.1.2 side2
  have k3 := badCard hBC (tw one1 q₁) Q P2 g1.1.1 g1.1.2.1 side3
  have k4 := badCard hBC (tw chi8 q₁) Q P2 g2.1.1 g2.1.2.1 side4
  have hP2 := (hMS2 one1).1
  have hp2pos : (0 : ℝ) < (P2.card : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hX2 _) hP2
  obtain ⟨d, hdP, hdB, hdS⟩ := markov_discard_bound P2
    ((badSet one1 Q P2 ∪ badSet chi8 Q P2) ∪ (badSet (tw one1 q₁) Q P2 ∪ badSet (tw chi8 q₁) Q P2)) 2
    (fun j q => if j = 0 then SS one1 x q else SS (tw one1 q₁) x q) V t htpos
    (by
      intro j
      by_cases hj : j = 0
      · simp only [hj, if_true]; exact (hMS2 one1).2
      · simp only [hj, if_false]; exact (hMS2 (tw one1 q₁)).2)
    (by
      have h1 : ((((badSet one1 Q P2 ∪ badSet chi8 Q P2) ∪
          (badSet (tw one1 q₁) Q P2 ∪ badSet (tw chi8 q₁) Q P2)).card : ℕ) : ℝ) ≤
          (((badSet one1 Q P2).card : ℝ) + ((badSet chi8 Q P2).card : ℝ)) +
          (((badSet (tw one1 q₁) Q P2).card : ℝ) + ((badSet (tw chi8 q₁) Q P2).card : ℝ)) := by
        exact_mod_cast (Finset.card_union_le _ _).trans
          (Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _))
      have h2 := mul_le_mul_of_nonneg_right hr hp2pos.le
      push_cast
      linarith)
  simp only [Finset.mem_union, not_or] at hdB
  obtain ⟨⟨nb1, nb2⟩, nb3, nb4⟩ := hdB
  obtain ⟨dp, d16, dM, dlo, dhi, -, -, -⟩ := hP2mem d hdP
  have hF2 : Fact d.Prime := ⟨dp⟩
  have dne2 : d ≠ 2 := by omega
  have dS0 : SS one1 x d ≤ t := le_trans (le_abs_self _) (by simpa using hdS 0)
  have dS1 : SS (tw one1 q₁) x d ≤ t := le_trans (le_abs_self _) (by simpa using hdS 1)
  have g3 := goodOf one1 Q P2 d trivial_character_primitive trivial_character_sq dne2 (side1 d hdP).2.1 (side1 d hdP).2.2 hdP nb1
  have g4 := goodOf chi8 Q P2 d twist_is_primitive.1.1 twist_is_primitive.1.2 dne2 (side2 d hdP).2.1 (side2 d hdP).2.2
    hdP nb2
  have g5 := goodOf (tw one1 q₁) Q P2 d g1.1.1 g1.1.2.1 dne2 (side3 d hdP).2.1 (side3 d hdP).2.2 hdP nb3
  have g6 := goodOf (tw chi8 q₁) Q P2 d g2.1.1 g2.1.2.1 dne2 (side4 d hdP).2.1 (side4 d hdP).2.2 hdP nb4
  obtain ⟨sp1, sp2⟩ := class_splits y q₁ d q1p d16 dM
  exact ⟨q₁, d, hF1, hF2, q18, d16, q1lo, q1hi, dlo, dhi, sp1, sp2, g1.1, g2.1, g3.1, g4.1, g5.1, g6.1,
    gBound hBT hx2 hx1 a6 a7 c7 one1 q₁ g1 q1S,
    gBound hBT hx2 hx1 c4 c5 c7 one1 d g3 dS0,
    gBound hBT hx2 hx1 c4 c5 c7 (tw one1 q₁) d g5 dS1⟩

end Formalism.HermitianLattices.ZeroFreeRegionGL2
