import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.ConcaveTwist

noncomputable def twShift (T : ℝ) : ℝ := Real.log (1 + Real.exp (-T))

noncomputable def twV (T y : ℝ) : ℝ := y + twShift T - Real.log (1 + Real.exp (y - T))

noncomputable def twP (T y : ℝ) : ℝ := (1 + Real.exp (y - T))⁻¹

noncomputable def twEta (T y : ℝ) : ℝ := 2 + twV T y + Real.log (1 + twV T y)

noncomputable def twEta1 (T y : ℝ) : ℝ := twP T y * (1 + (1 + twV T y)⁻¹)

noncomputable def twEta2 (T y : ℝ) : ℝ :=
  -(twP T y * (1 - twP T y)) * (1 + (1 + twV T y)⁻¹) - twP T y * (twP T y * ((1 + twV T y) ^ 2)⁻¹)

/- English proof (translation)
The claim follows from `inv_pos.mpr (by positivity)`.
-/
lemma logistic_pos (T y : ℝ) : 0 < twP T y := inv_pos.mpr (by positivity)

/- English proof (translation)
Unfold `twP; exact mul_inv_cancel₀ (by positivity)`.
-/
lemma twistMap_add_mul (T y : ℝ) : (1 + Real.exp (y - T)) * twP T y = 1 := by
  unfold twP; exact mul_inv_cancel₀ (by positivity)

/- English proof (translation)
Establish `h` using `twistMap_add_mul T y`. Use `logistic_pos T y` as an intermediate fact. Use polynomial arithmetic with `[Real.exp_pos (y - T)]`.
-/
lemma logistic_lt_one (T y : ℝ) : twP T y < 1 := by
  have h := twistMap_add_mul T y
  have := logistic_pos T y
  nlinarith [Real.exp_pos (y - T)]

/- English proof (translation)
The claim follows from `Real.log_nonneg (by linarith [Real.exp_pos (-T)])`.
-/
lemma twShift_nonneg (T : ℝ) : 0 ≤ twShift T :=
  Real.log_nonneg (by linarith [Real.exp_pos (-T)])

/- English proof (translation)
Establish `h1` using `Real.log_le_sub_one_of_pos (show 0 < 1 + Real.exp (-T) by positivity)`. Establish `h2 : Real.exp (-T) ≤ 1` using `Real.exp_le_one_iff.mpr (by linarith)`. Unfold `twShift`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma twShift_le_one (T : ℝ) (hT : 0 ≤ T) : twShift T ≤ 1 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.exp (-T) by positivity)
  have h2 : Real.exp (-T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold twShift; linarith

/- English proof (translation)
Establish `: Real.log (1 + Real.exp (y - T)) ≤ twShift T`. Unfold `twShift`. Apply `Real.log_le_log (by positivity)` to reduce the goal to its premises. Use `Real.exp_le_exp.mpr (show y - T ≤ -T by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `twV`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma twV_ge_self (T y : ℝ) (hy : y ≤ 0) : y ≤ twV T y := by
  have : Real.log (1 + Real.exp (y - T)) ≤ twShift T := by
    unfold twShift
    apply Real.log_le_log (by positivity)
    have := Real.exp_le_exp.mpr (show y - T ≤ -T by linarith)
    linarith
  unfold twV; linarith

/- English proof (translation)
Establish `he : Real.exp (y - T) = Real.exp y * Real.exp (-T)`. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form. Establish `h1 : 1 ≤ Real.exp y` using `Real.one_le_exp hy`. Establish `: Real.log (1 + Real.exp (y - T)) ≤ y + twShift T`.

Establish `hr : y + twShift T = Real.log (Real.exp y * (1 + Real.exp (-T)))`. Rewrite using `[Real.log_mul (Real.exp_pos y).ne' (by positivity), Real.log_exp]; rfl`. Rewrite using `[hr]`. Apply `Real.log_le_log (by positivity)` to reduce the goal to its premises. Rewrite using `[he]`.

Use polynomial arithmetic with `[Real.exp_pos (-T)]`. Unfold `twV`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma twV_nonneg (T y : ℝ) (hy : 0 ≤ y) : 0 ≤ twV T y := by
  have he : Real.exp (y - T) = Real.exp y * Real.exp (-T) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : 1 ≤ Real.exp y := Real.one_le_exp hy
  have : Real.log (1 + Real.exp (y - T)) ≤ y + twShift T := by
    have hr : y + twShift T = Real.log (Real.exp y * (1 + Real.exp (-T))) := by
      rw [Real.log_mul (Real.exp_pos y).ne' (by positivity), Real.log_exp]; rfl
    rw [hr]
    apply Real.log_le_log (by positivity)
    rw [he]; nlinarith [Real.exp_pos (-T)]
  unfold twV; linarith

/- English proof (translation)
Establish `: y - T ≤ Real.log (1 + Real.exp (y - T))`. Combine the equalities or inequalities in the displayed calculation. Use `twShift_le_one T hT` as an intermediate fact. Unfold `twV`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma twV_le (T y : ℝ) (hT : 0 ≤ T) : twV T y ≤ T + 1 := by
  have : y - T ≤ Real.log (1 + Real.exp (y - T)) := by
    calc y - T = Real.log (Real.exp (y - T)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by linarith)
  have := twShift_le_one T hT
  unfold twV; linarith

/- English proof (translation)
Establish `: twShift T ≤ Real.log (1 + Real.exp (y - T))`. Unfold `twShift`. Apply `Real.log_le_log (by positivity)` to reduce the goal to its premises. Use `Real.exp_le_exp.mpr (show -T ≤ y - T by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `twV`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma twV_le_self (T y : ℝ) (hy : 0 ≤ y) : twV T y ≤ y := by
  have : twShift T ≤ Real.log (1 + Real.exp (y - T)) := by
    unfold twShift
    apply Real.log_le_log (by positivity)
    have := Real.exp_le_exp.mpr (show -T ≤ y - T by linarith)
    linarith
  unfold twV; linarith

/- English proof (translation)
Break down `le_total y 0 with h | h` into its components or cases. Combine the linear relations using `[twV_ge_self T y h]`. Combine the linear relations using `[twV_nonneg T y h]`.
-/
lemma twV_gt (T y : ℝ) (hy : -1/4 < y) : -1/4 < twV T y := by
  rcases le_total y 0 with h | h
  · linarith [twV_ge_self T y h]
  · linarith [twV_nonneg T y h]

/- English proof (translation)
Use `set q := Real.exp (y - T) with hq`. Establish `hq0 : 0 < q` using `Real.exp_pos _`. Establish `he2 : 2 ≤ Real.exp 1` using `by linarith [Real.add_one_le_exp (1 : ℝ)]`. Establish `hqe : 1 ≤ q * Real.exp 1`. Rewrite using `[hq, ← Real.exp_add]; exact Real.one_le_exp (by linarith)`.

Establish `hE : Real.exp (y - T + 2) = q * Real.exp 1 * Real.exp 1`. Rewrite using `[show y - T + 2 = (y - T) + 1 + 1 by ring, Real.exp_add, Real.exp_add]`. Establish `: Real.log (1 + q) ≤ y - T + 2`. Combine the equalities or inequalities in the displayed calculation. Apply `Real.log_le_log (by positivity)` to reduce the goal to its premises.

Rewrite using `[hE]`. Use polynomial arithmetic with `[mul_nonneg hq0.le (show 0 ≤ Real.exp 1 * Real.exp 1 - Real.exp 1 - 1 by nlinarith)]`. Use `_ = y - T + 2 := Real.log_exp _`. Use `twShift_nonneg T` as an intermediate fact. Unfold `twV`.

Rewrite using `[← hq]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma twV_ge_T_sub_two (T y : ℝ) (h1 : T - 1 ≤ y) (h2 : y ≤ T + 1) : T - 2 ≤ twV T y := by
  set q := Real.exp (y - T) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have he2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hqe : 1 ≤ q * Real.exp 1 := by
    rw [hq, ← Real.exp_add]; exact Real.one_le_exp (by linarith)
  have hE : Real.exp (y - T + 2) = q * Real.exp 1 * Real.exp 1 := by
    rw [show y - T + 2 = (y - T) + 1 + 1 by ring, Real.exp_add, Real.exp_add]
  have : Real.log (1 + q) ≤ y - T + 2 := by
    calc Real.log (1 + q) ≤ Real.log (Real.exp (y - T + 2)) := by
          apply Real.log_le_log (by positivity)
          rw [hE]
          nlinarith [mul_nonneg hq0.le (show 0 ≤ Real.exp 1 * Real.exp 1 - Real.exp 1 - 1 by nlinarith)]
      _ = y - T + 2 := Real.log_exp _
  have := twShift_nonneg T
  unfold twV; rw [← hq]; linarith

/- English proof (translation)
Establish `h1 : HasDerivAt (fun y => Real.exp (y - T)) (Real.exp (y - T)) y`. Simplify using `using ((hasDerivAt_id y).sub_const T).exp`. Establish `h2 : HasDerivAt (fun y => Real.log (1 + Real.exp (y - T))) (Real.exp (y - T) / (1 + Real.exp (y - T))) y`. Simplify using `using (h1.const_add 1).log (by positivity)`. Establish `h3` using `((hasDerivAt_id y).add_const (twShift T)).sub h2`.

Use `h3.congr_deriv ?_` and prove the remaining obligations. Establish `: (1 + Real.exp (y - T)) ≠ 0` using `by positivity`. Unfold `twP`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hasDerivAt_twV (T y : ℝ) : HasDerivAt (twV T) (twP T y) y := by
  have h1 : HasDerivAt (fun y => Real.exp (y - T)) (Real.exp (y - T)) y := by
    simpa using ((hasDerivAt_id y).sub_const T).exp
  have h2 : HasDerivAt (fun y => Real.log (1 + Real.exp (y - T)))
      (Real.exp (y - T) / (1 + Real.exp (y - T))) y := by
    simpa using (h1.const_add 1).log (by positivity)
  have h3 := ((hasDerivAt_id y).add_const (twShift T)).sub h2
  refine h3.congr_deriv ?_
  have : (1 + Real.exp (y - T)) ≠ 0 := by positivity
  unfold twP; field_simp; ring

/- English proof (translation)
Establish `h1 : HasDerivAt (fun y => Real.exp (y - T)) (Real.exp (y - T)) y`. Simplify using `using ((hasDerivAt_id y).sub_const T).exp`. Establish `h2` using `(h1.const_add 1).inv (show (1 + Real.exp (y - T)) ≠ 0 by positivity)`. Use `h2.congr_deriv ?_` and prove the remaining obligations. Establish `: (1 + Real.exp (y - T)) ≠ 0` using `by positivity`.

Unfold `twP`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hasDerivAt_twP (T y : ℝ) : HasDerivAt (twP T) (-(twP T y * (1 - twP T y))) y := by
  have h1 : HasDerivAt (fun y => Real.exp (y - T)) (Real.exp (y - T)) y := by
    simpa using ((hasDerivAt_id y).sub_const T).exp
  have h2 := (h1.const_add 1).inv (show (1 + Real.exp (y - T)) ≠ 0 by positivity)
  refine h2.congr_deriv ?_
  have : (1 + Real.exp (y - T)) ≠ 0 := by positivity
  unfold twP; field_simp; ring

/- English proof (translation)
Establish `hv` using `hasDerivAt_twV T y`. Establish `h2` using `(hv.const_add 2).add ((hv.const_add 1).log h.ne')`. Use `h2.congr_deriv ?_` and prove the remaining obligations. Unfold `twEta1`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hasDerivAt_twEta (T y : ℝ) (h : 0 < 1 + twV T y) :
    HasDerivAt (twEta T) (twEta1 T y) y := by
  have hv := hasDerivAt_twV T y
  have h2 := (hv.const_add 2).add ((hv.const_add 1).log h.ne')
  refine h2.congr_deriv ?_
  unfold twEta1; ring

/- English proof (translation)
Establish `hv` using `hasDerivAt_twV T y`. Establish `hp` using `hasDerivAt_twP T y`. Establish `h2` using `hp.mul (((hv.const_add 1).inv h.ne').const_add 1)`. Use `h2.congr_deriv ?_` and prove the remaining obligations. Unfold `twEta2`.

Simplify using `only [Pi.inv_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hasDerivAt_twEta1 (T y : ℝ) (h : 0 < 1 + twV T y) :
    HasDerivAt (twEta1 T) (twEta2 T y) y := by
  have hv := hasDerivAt_twV T y
  have hp := hasDerivAt_twP T y
  have h2 := hp.mul (((hv.const_add 1).inv h.ne').const_add 1)
  refine h2.congr_deriv ?_
  unfold twEta2; simp only [Pi.inv_apply]; ring

/- English proof (translation)
Establish `h : ContDiff ℝ ∞ (fun y : ℝ => 1 + Real.exp (y - T))` using `contDiff_const.add ((contDiff_id.sub contDiff_const).exp)`. Conclude with `(contDiff_id.add contDiff_const).sub (h.log fun y => by positivity)`.
-/
lemma contDiff_twV (T : ℝ) : ContDiff ℝ ∞ (twV T) := by
  have h : ContDiff ℝ ∞ (fun y : ℝ => 1 + Real.exp (y - T)) :=
    contDiff_const.add ((contDiff_id.sub contDiff_const).exp)
  exact (contDiff_id.add contDiff_const).sub (h.log fun y => by positivity)

end GlobalTheory.ConcaveTwist

namespace GlobalTheory.ConcaveTwist

/- English proof (translation)
Establish `hv` using `contDiff_twV T`. Establish `h1 : ContDiff ℝ ∞ (fun y => 1 + twV T y)` using `contDiff_const.add hv`. Conclude with `((contDiff_const.add hv).contDiffOn).add (h1.contDiffOn.log fun y hy => by have := twV_gt T y hy; linarith)`.
-/
lemma contDiffOn_twEta (T : ℝ) : ContDiffOn ℝ ∞ (twEta T) (Set.Ioi (-1/4)) := by
  have hv := contDiff_twV T
  have h1 : ContDiff ℝ ∞ (fun y => 1 + twV T y) := contDiff_const.add hv
  exact ((contDiff_const.add hv).contDiffOn).add
    (h1.contDiffOn.log fun y hy => by have := twV_gt T y hy; linarith)

/- English proof (translation)
Establish `hv` using `twV_gt T y hy`. Establish `hw : 0 < 1 + twV T y` using `by linarith`. Establish `hl` using `Real.one_sub_inv_le_log_of_pos hw`. Establish `hi : (1 + twV T y)⁻¹ < 4/3`. Rewrite using `[inv_lt_comm₀ hw (by norm_num)]; linarith`.

Unfold `twEta`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma twEta_pos (T y : ℝ) (hy : -1/4 < y) : 0 < twEta T y := by
  have hv := twV_gt T y hy
  have hw : 0 < 1 + twV T y := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hw
  have hi : (1 + twV T y)⁻¹ < 4/3 := by
    rw [inv_lt_comm₀ hw (by norm_num)]; linarith
  unfold twEta; linarith

/- English proof (translation)
Establish `hv0` using `twV_nonneg T y hy`. Establish `hvm : twV T y ≤ min y (T + 1)` using `le_min (twV_le_self T y hy) (twV_le T y hT)`. Establish `hp0` using `logistic_pos T y`. Establish `hp1` using `logistic_lt_one T y`. Use `set v := twV T y with hvdef`.

Use `set p := twP T y with hpdef`. Use `set m := min y (T + 1) with hmdef`. Establish `hw : 0 < 1 + v` using `by linarith`. Use `set r := (1 + v)⁻¹ with hrdef`. Establish `hr0 : 0 < r` using `inv_pos.mpr hw`.

Establish `hwr : (1 + v) * r = 1` using `mul_inv_cancel₀ hw.ne'`. Establish `hr1 : r ≤ 1` using `by nlinarith`. Establish `hr2 : ((1 + v) ^ 2)⁻¹ = r ^ 2` using `by rw [inv_pow]`. Establish `hη1 : twEta1 T y = p * (1 + r)` using `rfl`. Establish `hη2 : -twEta2 T y = p * (1 - p) * (1 + r) + p ^ 2 * r ^ 2`.

Unfold `twEta2`. Rewrite using `[← hvdef, ← hpdef, hr2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hη : twEta T y = 2 + v + Real.log (1 + v)` using `rfl`. Establish `hlog0 : 0 ≤ Real.log (1 + v)` using `Real.log_nonneg (by linarith)`.

Establish `hlogv : Real.log (1 + v) ≤ v`. Use `Real.log_le_sub_one_of_pos hw` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hneg : 0 < -twEta2 T y`. Rewrite using `[hη2]; have := mul_pos (mul_pos hp0 (sub_pos.mpr hp1)) (by linarith : (0:ℝ) < 1 + r)`.

Check the signs of the components of the expression. Establish `key : (2 + v) * r = 1 + r` using `by linear_combination hwr`. Establish `key2 : ((2 + v) * r) ^ 2 = (1 + r) ^ 2` using `by rw [key]`. Establish `hratio : twEta1 T y ^ 2 / (-twEta2 T y) ≤ (2 + v) ^ 2`. Rewrite using `[div_le_iff₀ hneg]`.

Establish `e : (2 + v) ^ 2 * (-twEta2 T y) - twEta1 T y ^ 2 = (2 + v) ^ 2 * (p * (1 - p) * (1 + r))`. Rewrite using `[hη2, hη1]`. Take the linear combination `p ^ 2 * key2`. Establish `: 0 ≤ (2 + v) ^ 2 * (p * (1 - p) * (1 + r))`. Use `sub_pos.mpr hp1` as an intermediate fact.

Check the signs of the components of the expression. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hvm2 : v ^ 2 ≤ m ^ 2` using `pow_le_pow_left₀ hv0 hvm 2`. Use `⟨by rw [hη1]; positivity, by rw [hη1]; nlinarith, by rw [hη]; linarith, by linarith, by rw [hη]; linarith, ?_⟩` and prove the remaining obligations. Rewrite using `[hη]`.

Use polynomial arithmetic with `[sq_nonneg (v - 3/7)]`.
-/
lemma twEta_bounds (T y : ℝ) (hT : 0 ≤ T) (hy : 0 ≤ y) :
    0 ≤ twEta1 T y ∧ twEta1 T y ≤ 2 ∧ 2 ≤ twEta T y ∧ twEta2 T y < 0 ∧
      twEta T y ≤ 2 + 2 * min y (T + 1) ∧
      twEta T y + twEta1 T y ^ 2 / (-twEta2 T y) ≤ 8 * (1 + (min y (T + 1)) ^ 2) := by
  have hv0 := twV_nonneg T y hy
  have hvm : twV T y ≤ min y (T + 1) := le_min (twV_le_self T y hy) (twV_le T y hT)
  have hp0 := logistic_pos T y
  have hp1 := logistic_lt_one T y
  set v := twV T y with hvdef
  set p := twP T y with hpdef
  set m := min y (T + 1) with hmdef
  have hw : 0 < 1 + v := by linarith
  set r := (1 + v)⁻¹ with hrdef
  have hr0 : 0 < r := inv_pos.mpr hw
  have hwr : (1 + v) * r = 1 := mul_inv_cancel₀ hw.ne'
  have hr1 : r ≤ 1 := by nlinarith
  have hr2 : ((1 + v) ^ 2)⁻¹ = r ^ 2 := by rw [inv_pow]
  have hη1 : twEta1 T y = p * (1 + r) := rfl
  have hη2 : -twEta2 T y = p * (1 - p) * (1 + r) + p ^ 2 * r ^ 2 := by
    unfold twEta2; rw [← hvdef, ← hpdef, hr2]; ring
  have hη : twEta T y = 2 + v + Real.log (1 + v) := rfl
  have hlog0 : 0 ≤ Real.log (1 + v) := Real.log_nonneg (by linarith)
  have hlogv : Real.log (1 + v) ≤ v := by
    have := Real.log_le_sub_one_of_pos hw; linarith
  have hneg : 0 < -twEta2 T y := by
    rw [hη2]; have := mul_pos (mul_pos hp0 (sub_pos.mpr hp1)) (by linarith : (0:ℝ) < 1 + r)
    positivity
  have key : (2 + v) * r = 1 + r := by linear_combination hwr
  have key2 : ((2 + v) * r) ^ 2 = (1 + r) ^ 2 := by rw [key]
  have hratio : twEta1 T y ^ 2 / (-twEta2 T y) ≤ (2 + v) ^ 2 := by
    rw [div_le_iff₀ hneg]
    have e : (2 + v) ^ 2 * (-twEta2 T y) - twEta1 T y ^ 2 = (2 + v) ^ 2 * (p * (1 - p) * (1 + r)) := by
      rw [hη2, hη1]; linear_combination p ^ 2 * key2
    have : 0 ≤ (2 + v) ^ 2 * (p * (1 - p) * (1 + r)) := by
      have := sub_pos.mpr hp1; positivity
    linarith
  have hvm2 : v ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ hv0 hvm 2
  refine ⟨by rw [hη1]; positivity, by rw [hη1]; nlinarith, by rw [hη]; linarith, by linarith,
    by rw [hη]; linarith, ?_⟩
  rw [hη]
  nlinarith [sq_nonneg (v - 3/7)]

/- English proof (translation)
Establish `hv` using `twV_ge_T_sub_two T y h1 h2`. Establish `hv0 : 0 ≤ twV T y` using `by linarith`. Establish `hp0` using `logistic_pos T y`. Establish `hp1` using `logistic_lt_one T y`. Establish `hpw` using `twistMap_add_mul T y`.

Use `set v := twV T y with hvdef`. Use `set p := twP T y with hpdef`. Use `set q := Real.exp (y - T) with hq`. Establish `hq0 : 0 < q` using `Real.exp_pos _`. Establish `he3 : Real.exp 1 < 3` using `by linarith [Real.exp_one_lt_d9]`.

Establish `hq3 : q ≤ 3`. Establish `: q ≤ Real.exp 1` using `Real.exp_le_exp.mpr (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hqe : 1 ≤ q * Real.exp 1`. Rewrite using `[hq, ← Real.exp_add]; exact Real.one_le_exp (by linarith)`.

Establish `hq13 : 1 / 3 ≤ q` using `by nlinarith`. Establish `hw : 0 < 1 + v` using `by linarith`. Use `set r := (1 + v)⁻¹ with hrdef`. Establish `hr0 : 0 < r` using `inv_pos.mpr hw`. Establish `hr2 : ((1 + v) ^ 2)⁻¹ = r ^ 2` using `by rw [inv_pow]`.

Establish `hη2 : -twEta2 T y = p * (1 - p) * (1 + r) + p ^ 2 * r ^ 2`. Unfold `twEta2`. Rewrite using `[← hvdef, ← hpdef, hr2]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1p : 1 - p = q * p` using `by linear_combination (-1 : ℝ) * hpw`.

Establish `hpw2 : ((1 + q) * p) ^ 2 = 1` using `by rw [hpw]; norm_num`. Establish `e : q * p ^ 2 * 16 - 3 = p ^ 2 * (3 * q - 1) * (3 - q)`. Take the linear combination `3 * hpw2`. Establish `hmain : 3 / 16 ≤ p * (1 - p)`. Rewrite using `[h1p]`.

Establish `: 0 ≤ p ^ 2 * (3 * q - 1) * (3 - q)`. Establish `a : 0 ≤ 3 * q - 1` using `by linarith`. Establish `b : 0 ≤ 3 - q` using `by linarith`. Check the signs of the components of the expression. Use the polynomial consequences of the given equalities and inequalities.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hη2]`. Establish `: 0 ≤ p * (1 - p) * r` using `by have := sub_pos.mpr hp1; positivity`. Use polynomial arithmetic with `[sq_nonneg (p * r)]`. Establish `hlog0 : 0 ≤ Real.log (1 + v)` using `Real.log_nonneg (by linarith) show T ≤ 2 + v + Real.log (1 + v)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma twEta_mid (T y : ℝ) (hT : 2 ≤ T) (h1 : T - 1 ≤ y) (h2 : y ≤ T + 1) :
    3 / 16 ≤ -twEta2 T y ∧ T ≤ twEta T y := by
  have hv := twV_ge_T_sub_two T y h1 h2
  have hv0 : 0 ≤ twV T y := by linarith
  have hp0 := logistic_pos T y
  have hp1 := logistic_lt_one T y
  have hpw := twistMap_add_mul T y
  set v := twV T y with hvdef
  set p := twP T y with hpdef
  set q := Real.exp (y - T) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have he3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have hq3 : q ≤ 3 := by
    have : q ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hqe : 1 ≤ q * Real.exp 1 := by
    rw [hq, ← Real.exp_add]; exact Real.one_le_exp (by linarith)
  have hq13 : 1 / 3 ≤ q := by nlinarith
  have hw : 0 < 1 + v := by linarith
  set r := (1 + v)⁻¹ with hrdef
  have hr0 : 0 < r := inv_pos.mpr hw
  have hr2 : ((1 + v) ^ 2)⁻¹ = r ^ 2 := by rw [inv_pow]
  have hη2 : -twEta2 T y = p * (1 - p) * (1 + r) + p ^ 2 * r ^ 2 := by
    unfold twEta2; rw [← hvdef, ← hpdef, hr2]; ring
  have h1p : 1 - p = q * p := by linear_combination (-1 : ℝ) * hpw
  have hpw2 : ((1 + q) * p) ^ 2 = 1 := by rw [hpw]; norm_num
  have e : q * p ^ 2 * 16 - 3 = p ^ 2 * (3 * q - 1) * (3 - q) := by
    linear_combination 3 * hpw2
  have hmain : 3 / 16 ≤ p * (1 - p) := by
    rw [h1p]
    have : 0 ≤ p ^ 2 * (3 * q - 1) * (3 - q) := by
      have a : 0 ≤ 3 * q - 1 := by linarith
      have b : 0 ≤ 3 - q := by linarith
      positivity
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [hη2]
    have : 0 ≤ p * (1 - p) * r := by have := sub_pos.mpr hp1; positivity
    nlinarith [sq_nonneg (p * r)]
  · have hlog0 : 0 ≤ Real.log (1 + v) := Real.log_nonneg (by linarith)
    show T ≤ 2 + v + Real.log (1 + v)
    linarith

end GlobalTheory.ConcaveTwist

open GlobalTheory.ConcaveTwist in

/- English proof (translation)
Introduce `T hT`. Use `⟨twEta T, twEta1 T, twEta2 T, contDiffOn_twEta T, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Establish `hw : 0 < 1 + twV T y` using `by linarith [twV_gt T y hy]`. Conclude with `⟨twEta_pos T y hy, hasDerivAt_twEta T y hw, hasDerivAt_twEta1 T y hw⟩`.

Introduce `y hy`. Conclude with `twEta_bounds T y (by linarith) hy`. Introduce `y h1 h2`. Conclude with `twEta_mid T y (by linarith) h1 h2`.
-/
theorem GlobalTheory.concave_twist_exists : ∀ T : ℝ, 300 ≤ T → ∃ η η1 η2 : ℝ → ℝ, ContDiffOn ℝ ∞ η (Set.Ioi (-1/4)) ∧ (∀ y, -1/4 < y → 0 < η y ∧ HasDerivAt η (η1 y) y ∧ HasDerivAt η1 (η2 y) y) ∧ (∀ y, 0 ≤ y → 0 ≤ η1 y ∧ η1 y ≤ 2 ∧ 2 ≤ η y ∧ η2 y < 0 ∧ η y ≤ 2 + 2 * min y (T + 1) ∧ η y + η1 y ^ 2 / (-η2 y) ≤ 8 * (1 + (min y (T + 1)) ^ 2)) ∧ (∀ y, T - 1 ≤ y → y ≤ T + 1 → 3 / 16 ≤ -η2 y ∧ T ≤ η y) := by
  intro T hT
  refine ⟨twEta T, twEta1 T, twEta2 T, contDiffOn_twEta T, ?_, ?_, ?_⟩
  · intro y hy
    have hw : 0 < 1 + twV T y := by linarith [twV_gt T y hy]
    exact ⟨twEta_pos T y hy, hasDerivAt_twEta T y hw, hasDerivAt_twEta1 T y hw⟩
  · intro y hy
    exact twEta_bounds T y (by linarith) hy
  · intro y h1 h2
    exact twEta_mid T y (by linarith) h1 h2
