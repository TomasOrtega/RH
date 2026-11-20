import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TwoHundredLeRadius
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DensityNumericalFacts
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ThresholdFinalFacts
import Formalism.PolynomialDimension.DigitClassCount

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

/- English proof (translation)
Use `set u := e / wa with hu`. Use `set v := e / wb with hv`. Establish `hu0 : 0 ≤ u` using `div_nonneg he hwa.le`. Establish `hv0 : 0 ≤ v` using `div_nonneg he hwb.le`. Establish `hN1 : (1 : ℝ) ≤ N` using `by exact_mod_cast hN`.

Establish `hs' : (N : ℝ) * x1 + N * x2 + N * u + N * v ≤ 1 / 2` using `by nlinarith`. Establish `hp1 : 0 ≤ (N : ℝ) * u` using `by positivity`. Establish `hp2 : 0 ≤ (N : ℝ) * v` using `by positivity`. Establish `hp3 : 0 ≤ (N : ℝ) * x1` using `by positivity`. Establish `hp4 : 0 ≤ (N : ℝ) * x2` using `by positivity`.

Establish `hu1 : u ≤ 1` using `by nlinarith`. Establish `hv1 : v ≤ 1` using `by nlinarith`. Establish `hx1 : x1 ≤ 1` using `by nlinarith`. Establish `hx2 : x2 ≤ 1` using `by nlinarith`. Establish `hwa' : wa + e = wa * (1 + u)` using `by rw [hu]; field_simp`.

Establish `hwb' : wb + e = wb * (1 + v)` using `by rw [hv]; field_simp`. Rewrite using `[hwa', hwb', mul_pow, mul_pow, mul_pow]`. Establish `hB : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → (1 + z) ^ N * (1 - N * z) ≤ 1`. Introduce `z hz0 hz1`. Establish `hb` using `one_add_mul_le_pow (a := -z) (by linarith) N`.

Establish `hzz : (1 + -z) ^ N = (1 - z) ^ N` using `by ring`. Establish `h1 : (1 + z) ^ N * (1 - z) ^ N ≤ 1`. Rewrite using `[← mul_pow]; exact pow_le_one₀ (by nlinarith) (by nlinarith)`. Establish `h2 : 0 ≤ (1 + z) ^ N` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Establish `hC : ∀ x : ℝ, x ≤ 1 → 1 - N * x ≤ (1 - x) ^ N`. Introduce `x hx1`. Establish `hb` using `one_add_mul_le_pow (a := -x) (by linarith) N`. Establish `hxx : (1 + -x) ^ N = (1 - x) ^ N` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `ha` using `hB u hu0 hu1`. Establish `hb` using `hB v hv0 hv1`. Establish `hc` using `hC x1 hx1`. Establish `hd` using `hC x2 hx2`. Establish `hA0 : 0 ≤ (1 + u) ^ N` using `by positivity`.

Establish `hB0 : 0 ≤ (1 + v) ^ N` using `by positivity`. Establish `e1 : 1 - N * u - N * v ≤ (1 - N * u) * (1 - N * v)` using `by nlinarith [mul_nonneg hp1 hp2]`. Establish `e2 : 1 - N * x1 - N * x2 ≤ (1 - N * x1) * (1 - N * x2)` using `by nlinarith [mul_nonneg hp3 hp4]`. Establish `e3 : (1 - N * u - N * v) * (1 - N * x1 - N * x2) ≤ (1 - N * u) * (1 - N * v) * ((1 - N * x1) * (1 - N * x2))` using `mul_le_mul e1 e2 (by linarith) (by nlinarith)`. Establish `e4 : 1 - (N * u + N * v) - (N * x1 + N * x2) ≤ (1 - N * u - N * v) * (1 - N * x1 - N * x2)`.

Use polynomial arithmetic with `[mul_nonneg (add_nonneg hp1 hp2) (add_nonneg hp3 hp4)]`. Establish `hprod : 1 ≤ 2 * ((1 - N * u) * (1 - N * v) * ((1 - N * x1) * (1 - N * x2)))` using `by linarith`. Establish `hAB : (1 + u) ^ N * (1 + v) ^ N * ((1 - N * u) * (1 - N * v)) ≤ 1`. Use `mul_le_one₀ ha (mul_nonneg hB0 (by linarith)) hb` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.

Establish `hCD : (1 - N * x1) * (1 - N * x2) ≤ (1 - x1) ^ N * (1 - x2) ^ N` using `mul_le_mul hc hd (by linarith) (le_trans (by linarith) hc)`. Establish `key : (1 + u) ^ N * (1 + v) ^ N ≤ 2 * ((1 - x1) ^ N * (1 - x2) ^ N)`. Establish `hγδ : 0 ≤ (1 - N * x1) * (1 - N * x2)` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Establish `hw : 0 ≤ wa ^ N * wb ^ N` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem dens_abs (N : ℕ) (hN : 1 ≤ N) (x1 x2 wa wb e : ℝ) (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (hwa : 0 < wa) (hwb : 0 < wb)
    (he : 0 ≤ e) (hs : (N : ℝ) * (x1 + x2 + e / wa + e / wb) ≤ 1 / 2) :
    (wa + e) ^ N * (wb + e) ^ N ≤ 2 * ((1 - x1) * (1 - x2)) ^ N * (wa ^ N * wb ^ N) := by
  set u := e / wa with hu
  set v := e / wb with hv
  have hu0 : 0 ≤ u := div_nonneg he hwa.le
  have hv0 : 0 ≤ v := div_nonneg he hwb.le
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs' : (N : ℝ) * x1 + N * x2 + N * u + N * v ≤ 1 / 2 := by nlinarith
  have hp1 : 0 ≤ (N : ℝ) * u := by positivity
  have hp2 : 0 ≤ (N : ℝ) * v := by positivity
  have hp3 : 0 ≤ (N : ℝ) * x1 := by positivity
  have hp4 : 0 ≤ (N : ℝ) * x2 := by positivity
  have hu1 : u ≤ 1 := by nlinarith
  have hv1 : v ≤ 1 := by nlinarith
  have hx1 : x1 ≤ 1 := by nlinarith
  have hx2 : x2 ≤ 1 := by nlinarith
  have hwa' : wa + e = wa * (1 + u) := by rw [hu]; field_simp
  have hwb' : wb + e = wb * (1 + v) := by rw [hv]; field_simp
  rw [hwa', hwb', mul_pow, mul_pow, mul_pow]

  have hB : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → (1 + z) ^ N * (1 - N * z) ≤ 1 := by
    intro z hz0 hz1
    have hb := one_add_mul_le_pow (a := -z) (by linarith) N
    have hzz : (1 + -z) ^ N = (1 - z) ^ N := by ring
    have h1 : (1 + z) ^ N * (1 - z) ^ N ≤ 1 := by
      rw [← mul_pow]; exact pow_le_one₀ (by nlinarith) (by nlinarith)
    have h2 : 0 ≤ (1 + z) ^ N := by positivity
    calc (1 + z) ^ N * (1 - N * z) ≤ (1 + z) ^ N * (1 - z) ^ N :=
          mul_le_mul_of_nonneg_left (by linarith) h2
      _ ≤ 1 := h1
  have hC : ∀ x : ℝ, x ≤ 1 → 1 - N * x ≤ (1 - x) ^ N := by
    intro x hx1
    have hb := one_add_mul_le_pow (a := -x) (by linarith) N
    have hxx : (1 + -x) ^ N = (1 - x) ^ N := by ring
    linarith
  have ha := hB u hu0 hu1
  have hb := hB v hv0 hv1
  have hc := hC x1 hx1
  have hd := hC x2 hx2
  have hA0 : 0 ≤ (1 + u) ^ N := by positivity
  have hB0 : 0 ≤ (1 + v) ^ N := by positivity

  have e1 : 1 - N * u - N * v ≤ (1 - N * u) * (1 - N * v) := by nlinarith [mul_nonneg hp1 hp2]
  have e2 : 1 - N * x1 - N * x2 ≤ (1 - N * x1) * (1 - N * x2) := by nlinarith [mul_nonneg hp3 hp4]
  have e3 : (1 - N * u - N * v) * (1 - N * x1 - N * x2) ≤
      (1 - N * u) * (1 - N * v) * ((1 - N * x1) * (1 - N * x2)) :=
    mul_le_mul e1 e2 (by linarith) (by nlinarith)
  have e4 : 1 - (N * u + N * v) - (N * x1 + N * x2) ≤ (1 - N * u - N * v) * (1 - N * x1 - N * x2) := by
    nlinarith [mul_nonneg (add_nonneg hp1 hp2) (add_nonneg hp3 hp4)]
  have hprod : 1 ≤ 2 * ((1 - N * u) * (1 - N * v) * ((1 - N * x1) * (1 - N * x2))) := by linarith
  have hAB : (1 + u) ^ N * (1 + v) ^ N * ((1 - N * u) * (1 - N * v)) ≤ 1 := by
    have := mul_le_one₀ ha (mul_nonneg hB0 (by linarith)) hb
    calc (1 + u) ^ N * (1 + v) ^ N * ((1 - N * u) * (1 - N * v))
        = (1 + u) ^ N * (1 - N * u) * ((1 + v) ^ N * (1 - N * v)) := by ring
      _ ≤ 1 := this
  have hCD : (1 - N * x1) * (1 - N * x2) ≤ (1 - x1) ^ N * (1 - x2) ^ N :=
    mul_le_mul hc hd (by linarith) (le_trans (by linarith) hc)
  have key : (1 + u) ^ N * (1 + v) ^ N ≤ 2 * ((1 - x1) ^ N * (1 - x2) ^ N) := by
    have hγδ : 0 ≤ (1 - N * x1) * (1 - N * x2) := by nlinarith
    calc (1 + u) ^ N * (1 + v) ^ N
        ≤ (1 + u) ^ N * (1 + v) ^ N *
            (2 * ((1 - N * u) * (1 - N * v) * ((1 - N * x1) * (1 - N * x2)))) :=
          le_mul_of_one_le_right (mul_nonneg hA0 hB0) hprod
      _ = 2 * ((1 - N * x1) * (1 - N * x2)) *
            ((1 + u) ^ N * (1 + v) ^ N * ((1 - N * u) * (1 - N * v))) := by ring
      _ ≤ 2 * ((1 - N * x1) * (1 - N * x2)) * 1 :=
          mul_le_mul_of_nonneg_left hAB (by linarith)
      _ ≤ 2 * ((1 - x1) ^ N * (1 - x2) ^ N) := by linarith
  have hw : 0 ≤ wa ^ N * wb ^ N := by positivity
  calc wa ^ N * (1 + u) ^ N * (wb ^ N * (1 + v) ^ N)
      = (1 + u) ^ N * (1 + v) ^ N * (wa ^ N * wb ^ N) := by ring
    _ ≤ 2 * ((1 - x1) ^ N * (1 - x2) ^ N) * (wa ^ N * wb ^ N) := mul_le_mul_of_nonneg_right key hw

/- English proof (translation)
Establish `hNY : 2 ≤ N * Y` using `by nlinarith`. Establish `hL2 : Real.log 2 ≤ Real.log (N * Y)` using `Real.log_le_log (by norm_num) hNY`. Establish `hlog2` using `Real.log_two_gt_d9`. Use `set L := Real.log (N * Y) with hL`. Establish `hexpL : Real.exp L = N * Y` using `Real.exp_log (by linarith)`.

Establish `h1 : N ^ 2 ≤ Real.exp (2 * L)`. Establish `hNY1 : N ≤ N * Y` using `by nlinarith`. Rewrite using `[show 2 * L = L + L by ring, Real.exp_add, hexpL, sq]`. Conclude with `mul_le_mul hNY1 hNY1 (by linarith) (by linarith)`. Establish `h2 : 1 + 2 * L / 3 ≤ Real.exp (2 * L / 3)` using `by linarith [Real.add_one_le_exp (2 * L / 3)]`.

Establish `h3 : Real.exp (2 * L) * Real.exp (2 * L / 3) ≤ Real.exp (La / 3)`. Rewrite using `[← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)`. Establish `h4 : N ^ 2 * (1 + 2 * L / 3) ≤ Real.exp (La / 3)` using `le_trans (mul_le_mul h1 h2 (by linarith) (Real.exp_pos _).le) h3`. Establish `h5 : N ^ 2 * 1.46 ≤ Real.exp (La / 3)` using `le_trans (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg N)) h4`. Establish `hpos : 0 < Real.exp (La / 3)` using `Real.exp_pos _`.

Rewrite using `[show -La / 3 = -(La / 3) by ring, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem Nexp_le (N Y La : ℝ) (hN : 2 ≤ N) (hY : 1 ≤ Y) (hLa : 8 * Real.log (N * Y) ≤ La) :
    N * Real.exp (-La / 3) ≤ 0.36 := by
  have hNY : 2 ≤ N * Y := by nlinarith
  have hL2 : Real.log 2 ≤ Real.log (N * Y) := Real.log_le_log (by norm_num) hNY
  have hlog2 := Real.log_two_gt_d9
  set L := Real.log (N * Y) with hL
  have hexpL : Real.exp L = N * Y := Real.exp_log (by linarith)
  have h1 : N ^ 2 ≤ Real.exp (2 * L) := by
    have hNY1 : N ≤ N * Y := by nlinarith
    rw [show 2 * L = L + L by ring, Real.exp_add, hexpL, sq]
    exact mul_le_mul hNY1 hNY1 (by linarith) (by linarith)
  have h2 : 1 + 2 * L / 3 ≤ Real.exp (2 * L / 3) := by linarith [Real.add_one_le_exp (2 * L / 3)]
  have h3 : Real.exp (2 * L) * Real.exp (2 * L / 3) ≤ Real.exp (La / 3) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have h4 : N ^ 2 * (1 + 2 * L / 3) ≤ Real.exp (La / 3) :=
    le_trans (mul_le_mul h1 h2 (by linarith) (Real.exp_pos _).le) h3
  have h5 : N ^ 2 * 1.46 ≤ Real.exp (La / 3) :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg N)) h4
  have hpos : 0 < Real.exp (La / 3) := Real.exp_pos _
  rw [show -La / 3 = -(La / 3) by ring, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
  nlinarith

end Formalism.MainNotions.flipOneThree.Pf

end
