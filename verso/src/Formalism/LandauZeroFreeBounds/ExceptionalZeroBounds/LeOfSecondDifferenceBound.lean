import Mathlib

noncomputable section

namespace Formalism.ZeroFreeDirichlet

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `hy0 : 0 < y` using `by linarith`. Establish `hc2 : c₀ ^ 2 ≤ 1` using `pow_le_one₀ hc0.le hc01`. Establish `hL2 : Real.log 2 ≤ Real.log y` using `Real.log_le_log (by norm_num) hy`. Establish `hl2` using `Real.log_two_gt_d9`. Establish `hlogmul : Real.log (y * (1 + h)) = Real.log y + Real.log (1 + h)`.

Establish `hh0' : 0 < h` using `by rw [hh]; exact Real.exp_pos _`. Conclude with `Real.log_mul hy0.ne' (by linarith)`. Use `set L := Real.log y with hLdef`. Establish `hL0 : 0 < L` using `by linarith`. Use `set s := Real.sqrt L with hsdef`.

Establish `hs0 : 0 ≤ s` using `Real.sqrt_nonneg _`. Establish `hss : s ^ 2 = L` using `Real.sq_sqrt hL0.le`. Establish `hs_half : 1 / 2 ≤ s` using `by nlinarith`. Use `set g := Real.exp (-(c₀ / 4) * s) with hgdef`. Establish `hg0 : 0 < g` using `Real.exp_pos _`.

Establish `hg1 : g ≤ 1`. Rewrite using `[hgdef, Real.exp_le_one_iff]`. Establish `: 0 ≤ c₀ / 4 * s` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hhg : h = g * g`.

Rewrite using `[hh, hgdef, ← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hh0 : 0 < h` using `by rw [hhg]; positivity`. Establish `hhle : h ≤ g` using `by rw [hhg]; exact mul_le_of_le_one_left hg0.le hg1`.

Establish `hh1 : h ≤ 1` using `le_trans hhle hg1`. Establish `hyg : Real.exp (s ^ 2 / 2) ≤ y * g`. Establish `hyL : y = Real.exp L` using `(Real.exp_log hy0).symm`. Rewrite using `[hgdef, hyL, ← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hc01 hs0, mul_nonneg hs0 (sub_nonneg.mpr hs_half)]`. Establish `hq` using `Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 2 / 2)`. Establish `hB : L + 1 ≤ 2 * (y * g)`. Establish `: 0 ≤ (s ^ 2 / 2) ^ 2 / 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `ht` using `Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ c₀ / 4 * s by positivity)`. Establish `hgt : g * Real.exp (c₀ / 4 * s) = 1`. Rewrite using `[hgdef, ← Real.exp_add, show -(c₀ / 4) * s + c₀ / 4 * s = 0 by ring, Real.exp_zero]`. Establish `hA1 : g * (c₀ / 4 * s) ^ 2 ≤ 2`. Establish `h0 : 0 ≤ c₀ / 4 * s` using `by positivity`.

Establish `: (c₀ / 4 * s) ^ 2 ≤ 2 * Real.exp (c₀ / 4 * s)` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Establish `hA : c₀ ^ 2 * g * (L + 1) ≤ 33`. Establish `e : c₀ ^ 2 * g * (L + 1) = 16 * (g * (c₀ / 4 * s) ^ 2) + c₀ ^ 2 * g`. Rewrite using `[← hss]`.

Expand and normalize the polynomial expressions, which then agree. Establish `: c₀ ^ 2 * g ≤ 1` using `mul_le_one₀ hc2 hg0.le hg1`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA' : g * (L + 1) ≤ 33 / c₀ ^ 2`.

Rewrite using `[le_div_iff₀ (by positivity)]`. Establish `e : g * (L + 1) * c₀ ^ 2 = c₀ ^ 2 * g * (L + 1)` using `by ring`. Rewrite using `[e]`. Conclude with `hA`. Establish `hlog : Real.log (y * (1 + h)) ≤ L + 1`.

Rewrite using `[hlogmul]`. Use `Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + h)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hP : 0 < y * h` using `by positivity`. Establish `hyh1 : y * (1 + h) - y = y * h` using `by ring`.

Rewrite `hmain` using `[hyh1]`. Establish `T1 : (y * h + 1) * ((y * h) * Real.log (y * (1 + h))) ≤ (y * h) * ((y * h + 1) * (L + 1))`. Establish `: (y * h) * Real.log (y * (1 + h)) ≤ (y * h) * (L + 1)` using `mul_le_mul_of_nonneg_left hlog hP.le`. Combine the equalities or inequalities in the displayed calculation. Establish `T1' : (y * h + 1) * (L + 1) ≤ (33 / c₀ ^ 2 + 2) * (y * g)`.

Combine the equalities or inequalities in the displayed calculation. Establish `T2 : 2 * y ^ 2 * h ^ 2 ≤ (y * h) * (2 * (y * g))`. Establish `: y * h ≤ y * g` using `mul_le_mul_of_nonneg_left hhle hy0.le`. Combine the equalities or inequalities in the displayed calculation. Establish `hhh : (1 + h) * h ≤ 2 * g`.

Establish `h1 : h * h ≤ h` using `mul_le_of_le_one_left hh0.le hh1`. Establish `e : (1 + h) * h = h + h * h` using `by ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hCy : 0 ≤ C * y` using `mul_nonneg hC hy0.le`.

Establish `T3 : y * (C * (y * (1 + h)) * eY) ≤ (y * h) * (2 * C * (y * g))`. Establish `hk : 0 ≤ C * (y * (1 + h))` using `mul_nonneg hC (by positivity)`. Establish `: C * (y * (1 + h)) * eY ≤ C * (y * (1 + h)) * h ^ 2` using `mul_le_mul_of_nonneg_left heY hk`. Combine the equalities or inequalities in the displayed calculation. Establish `T4 : y * (1 + h) * (C * y * ey) ≤ (y * h) * (2 * C * (y * g))`.

Establish `hk : 0 ≤ y * (1 + h) * (C * y)` using `mul_nonneg (by positivity) hCy`. Establish `: y * (1 + h) * (C * y) * ey ≤ y * (1 + h) * (C * y) * h ^ 2` using `mul_le_mul_of_nonneg_left hey hk`. Combine the equalities or inequalities in the displayed calculation. Establish `T1''` using `mul_le_mul_of_nonneg_left T1' hP.le`. Establish `hfin : (33 / c₀ ^ 2 + 2) * (y * g) + 2 * (y * g) + 2 * C * (y * g) + 2 * C * (y * g) ≤ (128 / c₀ ^ 2 + 2 + 4 * C) * y * g`.

Establish `h95 : 2 ≤ 95 / c₀ ^ 2`. Rewrite using `[le_div_iff₀ (by positivity)]; linarith`. Use `mul_le_mul_of_nonneg_right h95 (by positivity : (0 : ℝ) ≤ y * g)` as an intermediate fact. Establish `e1 : (128 / c₀ ^ 2 + 2 + 4 * C) * y * g = (33 / c₀ ^ 2 + 2) * (y * g) + 95 / c₀ ^ 2 * (y * g) + 2 * C * (y * g) + 2 * C * (y * g)`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfin'` using `mul_le_mul_of_nonneg_left hfin hP.le`. Use `le_of_mul_le_mul_left ?_ hP` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma le_of_second_difference_bound {y c₀ C N eY ey h : ℝ} (hy : 2 ≤ y) (hc0 : 0 < c₀) (hc01 : c₀ ≤ 1) (hC : 0 ≤ C)
    (hh : h = Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)))
    (hey0 : 0 ≤ ey) (heY0 : 0 ≤ eY) (hey : ey ≤ h ^ 2) (heY : eY ≤ h ^ 2)
    (hmain : y * h * N ≤ (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h)))
        + 2 * y ^ 2 * h ^ 2 + y * (C * (y * (1 + h)) * eY) + y * (1 + h) * (C * y * ey)) :
    N ≤ (128 / c₀ ^ 2 + 2 + 4 * C) * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y)) := by
  have hy0 : 0 < y := by linarith
  have hc2 : c₀ ^ 2 ≤ 1 := pow_le_one₀ hc0.le hc01
  have hL2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hl2 := Real.log_two_gt_d9
  have hlogmul : Real.log (y * (1 + h)) = Real.log y + Real.log (1 + h) := by
    have hh0' : 0 < h := by rw [hh]; exact Real.exp_pos _
    exact Real.log_mul hy0.ne' (by linarith)
  set L := Real.log y with hLdef
  have hL0 : 0 < L := by linarith
  set s := Real.sqrt L with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = L := Real.sq_sqrt hL0.le
  have hs_half : 1 / 2 ≤ s := by nlinarith
  set g := Real.exp (-(c₀ / 4) * s) with hgdef
  have hg0 : 0 < g := Real.exp_pos _
  have hg1 : g ≤ 1 := by
    rw [hgdef, Real.exp_le_one_iff]
    have : 0 ≤ c₀ / 4 * s := by positivity
    linarith
  have hhg : h = g * g := by
    rw [hh, hgdef, ← Real.exp_add]; congr 1; ring
  have hh0 : 0 < h := by rw [hhg]; positivity
  have hhle : h ≤ g := by rw [hhg]; exact mul_le_of_le_one_left hg0.le hg1
  have hh1 : h ≤ 1 := le_trans hhle hg1
  have hyg : Real.exp (s ^ 2 / 2) ≤ y * g := by
    have hyL : y = Real.exp L := (Real.exp_log hy0).symm
    rw [hgdef, hyL, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc01 hs0, mul_nonneg hs0 (sub_nonneg.mpr hs_half)]
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 2 / 2)
  have hB : L + 1 ≤ 2 * (y * g) := by
    have : 0 ≤ (s ^ 2 / 2) ^ 2 / 2 := by positivity
    linarith
  have ht := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ c₀ / 4 * s by positivity)
  have hgt : g * Real.exp (c₀ / 4 * s) = 1 := by
    rw [hgdef, ← Real.exp_add, show -(c₀ / 4) * s + c₀ / 4 * s = 0 by ring, Real.exp_zero]
  have hA1 : g * (c₀ / 4 * s) ^ 2 ≤ 2 := by
    have h0 : 0 ≤ c₀ / 4 * s := by positivity
    have : (c₀ / 4 * s) ^ 2 ≤ 2 * Real.exp (c₀ / 4 * s) := by linarith
    calc g * (c₀ / 4 * s) ^ 2 ≤ g * (2 * Real.exp (c₀ / 4 * s)) :=
          mul_le_mul_of_nonneg_left this hg0.le
      _ = 2 * (g * Real.exp (c₀ / 4 * s)) := by ring
      _ = 2 := by rw [hgt]; ring
  have hA : c₀ ^ 2 * g * (L + 1) ≤ 33 := by
    have e : c₀ ^ 2 * g * (L + 1) = 16 * (g * (c₀ / 4 * s) ^ 2) + c₀ ^ 2 * g := by
      rw [← hss]; ring
    have : c₀ ^ 2 * g ≤ 1 := mul_le_one₀ hc2 hg0.le hg1
    rw [e]; linarith
  have hA' : g * (L + 1) ≤ 33 / c₀ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have e : g * (L + 1) * c₀ ^ 2 = c₀ ^ 2 * g * (L + 1) := by ring
    rw [e]; exact hA
  have hlog : Real.log (y * (1 + h)) ≤ L + 1 := by
    rw [hlogmul]
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + h)
    linarith
  have hP : 0 < y * h := by positivity
  have hyh1 : y * (1 + h) - y = y * h := by ring
  rw [hyh1] at hmain
  have T1 : (y * h + 1) * ((y * h) * Real.log (y * (1 + h))) ≤ (y * h) * ((y * h + 1) * (L + 1)) := by
    have : (y * h) * Real.log (y * (1 + h)) ≤ (y * h) * (L + 1) :=
      mul_le_mul_of_nonneg_left hlog hP.le
    calc (y * h + 1) * ((y * h) * Real.log (y * (1 + h))) ≤ (y * h + 1) * ((y * h) * (L + 1)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (y * h) * ((y * h + 1) * (L + 1)) := by ring
  have T1' : (y * h + 1) * (L + 1) ≤ (33 / c₀ ^ 2 + 2) * (y * g) := by
    calc (y * h + 1) * (L + 1) = (y * g) * (g * (L + 1)) + (L + 1) := by rw [hhg]; ring
      _ ≤ (y * g) * (33 / c₀ ^ 2) + 2 * (y * g) :=
          add_le_add (mul_le_mul_of_nonneg_left hA' (by positivity)) hB
      _ = (33 / c₀ ^ 2 + 2) * (y * g) := by ring
  have T2 : 2 * y ^ 2 * h ^ 2 ≤ (y * h) * (2 * (y * g)) := by
    have : y * h ≤ y * g := mul_le_mul_of_nonneg_left hhle hy0.le
    calc 2 * y ^ 2 * h ^ 2 = (y * h) * (2 * (y * h)) := by ring
      _ ≤ (y * h) * (2 * (y * g)) := mul_le_mul_of_nonneg_left (by linarith) hP.le
  have hhh : (1 + h) * h ≤ 2 * g := by
    have h1 : h * h ≤ h := mul_le_of_le_one_left hh0.le hh1
    have e : (1 + h) * h = h + h * h := by ring
    rw [e]; linarith
  have hCy : 0 ≤ C * y := mul_nonneg hC hy0.le
  have T3 : y * (C * (y * (1 + h)) * eY) ≤ (y * h) * (2 * C * (y * g)) := by
    have hk : 0 ≤ C * (y * (1 + h)) := mul_nonneg hC (by positivity)
    have : C * (y * (1 + h)) * eY ≤ C * (y * (1 + h)) * h ^ 2 := mul_le_mul_of_nonneg_left heY hk
    calc y * (C * (y * (1 + h)) * eY) ≤ y * (C * (y * (1 + h)) * h ^ 2) :=
          mul_le_mul_of_nonneg_left this hy0.le
      _ = (y * h) * (C * y * ((1 + h) * h)) := by ring
      _ ≤ (y * h) * (C * y * (2 * g)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhh hCy) hP.le
      _ = (y * h) * (2 * C * (y * g)) := by ring
  have T4 : y * (1 + h) * (C * y * ey) ≤ (y * h) * (2 * C * (y * g)) := by
    have hk : 0 ≤ y * (1 + h) * (C * y) := mul_nonneg (by positivity) hCy
    have : y * (1 + h) * (C * y) * ey ≤ y * (1 + h) * (C * y) * h ^ 2 :=
      mul_le_mul_of_nonneg_left hey hk
    calc y * (1 + h) * (C * y * ey) = y * (1 + h) * (C * y) * ey := by ring
      _ ≤ y * (1 + h) * (C * y) * h ^ 2 := this
      _ = (y * h) * (C * y * ((1 + h) * h)) := by ring
      _ ≤ (y * h) * (C * y * (2 * g)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhh hCy) hP.le
      _ = (y * h) * (2 * C * (y * g)) := by ring
  have T1'' := mul_le_mul_of_nonneg_left T1' hP.le
  have hfin : (33 / c₀ ^ 2 + 2) * (y * g) + 2 * (y * g) + 2 * C * (y * g) + 2 * C * (y * g) ≤
      (128 / c₀ ^ 2 + 2 + 4 * C) * y * g := by
    have h95 : 2 ≤ 95 / c₀ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have := mul_le_mul_of_nonneg_right h95 (by positivity : (0 : ℝ) ≤ y * g)
    have e1 : (128 / c₀ ^ 2 + 2 + 4 * C) * y * g =
        (33 / c₀ ^ 2 + 2) * (y * g) + 95 / c₀ ^ 2 * (y * g) + 2 * C * (y * g) + 2 * C * (y * g) := by
      ring
    rw [e1]; linarith
  have hfin' := mul_le_mul_of_nonneg_left hfin hP.le
  refine le_of_mul_le_mul_left ?_ hP
  linarith

/- English proof (translation)
Establish `hy0 : 0 < y` using `by linarith`. Establish `hL2 : Real.log 2 ≤ Real.log y` using `Real.log_le_log (by norm_num) hy`. Establish `hl2` using `Real.log_two_gt_d9`. Establish `hyL : y = Real.exp (Real.log y)` using `(Real.exp_log hy0).symm`. Use `set L := Real.log y with hLdef`.

Establish `hL0 : 0 < L` using `by linarith`. Use `set s := Real.sqrt L with hsdef`. Establish `hs0 : 0 ≤ s` using `Real.sqrt_nonneg _`. Establish `hss : s ^ 2 = L` using `Real.sq_sqrt hL0.le`. Establish `hs_half : 1 / 2 ≤ s` using `by nlinarith`.

Establish `hKL : K ≤ 2 * L` using `by nlinarith`. Establish `hlq' : lq ≤ s / 4`. Establish `: c₀ / 4 * s ≤ 1 / 4 * s` using `mul_le_mul_of_nonneg_right (by linarith) hs0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hKlq : K * lq ≤ (2 * L) * (s / 4)` using `mul_le_mul hKL hlq' hlq0 (by positivity)`.

Establish `hexp : Real.exp (s ^ 2 / 2) ≤ y * Real.exp (-(c₀ / 4) * s)`. Rewrite using `[hyL, ← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hc01 hs0, mul_nonneg hs0 (sub_nonneg.mpr hs_half)]`. Establish `hq` using `Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 2 / 2)`.

Establish `hpoly : (2 * L) * (s / 4) ≤ 16 * (1 + s ^ 2 / 2 + (s ^ 2 / 2) ^ 2 / 2)`. Rewrite using `[← hss]`. Use polynomial arithmetic with `[sq_nonneg (s ^ 2 - s), sq_nonneg s]`. Establish `e : 16 * y * Real.exp (-(c₀ / 4) * s) = 16 * (y * Real.exp (-(c₀ / 4) * s))` using `by ring`. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma mul_le_of_log_bounds {y c₀ K lq : ℝ} (hy : 2 ≤ y) (hc0 : 0 < c₀) (hc01 : c₀ ≤ 1)
    (hK : K * Real.log 2 ≤ Real.log y) (hK0 : 0 ≤ K) (hlq0 : 0 ≤ lq)
    (hlq : lq ≤ c₀ / 4 * Real.sqrt (Real.log y)) :
    K * lq ≤ 16 * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y)) := by
  have hy0 : 0 < y := by linarith
  have hL2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hl2 := Real.log_two_gt_d9
  have hyL : y = Real.exp (Real.log y) := (Real.exp_log hy0).symm
  set L := Real.log y with hLdef
  have hL0 : 0 < L := by linarith
  set s := Real.sqrt L with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = L := Real.sq_sqrt hL0.le
  have hs_half : 1 / 2 ≤ s := by nlinarith
  have hKL : K ≤ 2 * L := by nlinarith
  have hlq' : lq ≤ s / 4 := by
    have : c₀ / 4 * s ≤ 1 / 4 * s := mul_le_mul_of_nonneg_right (by linarith) hs0
    linarith
  have hKlq : K * lq ≤ (2 * L) * (s / 4) := mul_le_mul hKL hlq' hlq0 (by positivity)
  have hexp : Real.exp (s ^ 2 / 2) ≤ y * Real.exp (-(c₀ / 4) * s) := by
    rw [hyL, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc01 hs0, mul_nonneg hs0 (sub_nonneg.mpr hs_half)]
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 2 / 2)
  have hpoly : (2 * L) * (s / 4) ≤ 16 * (1 + s ^ 2 / 2 + (s ^ 2 / 2) ^ 2 / 2) := by
    rw [← hss]; nlinarith [sq_nonneg (s ^ 2 - s), sq_nonneg s]
  have e : 16 * y * Real.exp (-(c₀ / 4) * s) = 16 * (y * Real.exp (-(c₀ / 4) * s)) := by ring
  rw [e]
  linarith

end Formalism.ZeroFreeDirichlet
