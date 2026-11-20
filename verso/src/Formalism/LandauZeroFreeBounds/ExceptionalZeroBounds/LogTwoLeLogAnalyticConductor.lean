import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Conclude with `Nat.one_le_iff_ne_zero.2 (NeZero.ne q)` after adjusting the coercions.
-/
lemma one_le_modulus_real (q : ℕ) [NeZero q] : (1 : ℝ) ≤ q := by
  exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)

/- English proof (translation)
Establish `h1` using `one_le_modulus_real q`. Establish `h2` using `abs_nonneg t`. Conclude with `Real.log_le_log (by norm_num) (by nlinarith)`.
-/
lemma log_two_le_log_analytic_conductor (q : ℕ) [NeZero q] (t : ℝ) : Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have h1 := one_le_modulus_real q
  have h2 := abs_nonneg t
  exact Real.log_le_log (by norm_num) (by nlinarith)

/- English proof (translation)
Establish `h` using `Real.log_two_gt_d9`. Establish `h2` using `log_two_le_log_analytic_conductor q t`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma log_analytic_conductor_ge_const (q : ℕ) [NeZero q] (t : ℝ) : 69 / 100 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have h := Real.log_two_gt_d9
  have h2 := log_two_le_log_analytic_conductor q t
  linarith

/- English proof (translation)
Unfold `InRegion at h ⊢`. Establish `hL : 0 < Real.log ((q : ℝ) * (|s.im| + 2))` using `lt_of_lt_of_le (Real.log_pos (by norm_num)) (log_two_le_log_analytic_conductor q s.im)`. Establish `h2 : c₁ / 2 / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c₁ / Real.log ((q : ℝ) * (|s.im| + 2))`. Rewrite using `[div_div]`. Conclude with `div_le_div_of_nonneg_left hc.le hL (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma zero_free_region_mono_half {c₁ : ℝ} (hc : 0 < c₁) (q : ℕ) [NeZero q] (s : ℂ)
    (h : InRegion (c₁ / 2) q s) : InRegion c₁ q s := by
  unfold InRegion at h ⊢
  have hL : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) :=
    lt_of_lt_of_le (Real.log_pos (by norm_num)) (log_two_le_log_analytic_conductor q s.im)
  have h2 : c₁ / 2 / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c₁ / Real.log ((q : ℝ) * (|s.im| + 2)) := by
    rw [div_div]
    exact div_le_div_of_nonneg_left hc.le hL (by linarith)
  linarith

/- English proof (translation)
Rewrite `hw` using `[Metric.mem_closedBall, Complex.dist_eq]`. Establish `h1` using `Complex.abs_re_le_norm (w - z₀)`. Rewrite `h1` using `[Complex.sub_re]`. Establish `h2` using `neg_abs_le (w.re - z₀.re)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma re_ge_of_mem_closedBall {z₀ w : ℂ} {r : ℝ} (hw : w ∈ Metric.closedBall z₀ r) : z₀.re - r ≤ w.re := by
  rw [Metric.mem_closedBall, Complex.dist_eq] at hw
  have h1 := Complex.abs_re_le_norm (w - z₀)
  rw [Complex.sub_re] at h1
  have h2 := neg_abs_le (w.re - z₀.re)
  linarith

/- English proof (translation)
Rewrite `hw` using `[Metric.mem_closedBall, Complex.dist_eq]`. Use `norm_sub_norm_le w z₀` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma norm_le_norm_add_of_mem_closedBall' {z₀ w : ℂ} {r : ℝ} (hw : w ∈ Metric.closedBall z₀ r) : ‖w‖ ≤ ‖z₀‖ + r := by
  rw [Metric.mem_closedBall, Complex.dist_eq] at hw
  have := norm_sub_norm_le w z₀
  linarith

/- English proof (translation)
Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Establish `h1 : ‖(21 / 20 : ℂ)‖ = 21 / 20`. Rewrite using `[show (21 / 20 : ℂ) = ((21 / 20 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]`. Establish `h2 : ‖(t : ℂ) * I‖ = |t|`. Rewrite using `[norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]`.

Rewrite using `[h1, h2]`.
-/
lemma norm_disc_center_le (t : ℝ) : ‖(21 / 20 : ℂ) + t * I‖ ≤ 21 / 20 + |t| := by
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(21 / 20 : ℂ)‖ = 21 / 20 := by
    rw [show (21 / 20 : ℂ) = ((21 / 20 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num)]
  have h2 : ‖(t : ℂ) * I‖ = |t| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2]

/- English proof (translation)
Establish `hA2 : 0 < 2 * A` using `by linarith`. Establish `h1 : Real.log M ≤ Real.log (2 * A) + L`. Establish `h` using `Real.log_le_log (by linarith) hML`. Rewrite `h` using `[Real.log_mul hA2.ne' (Real.exp_pos L).ne', Real.log_exp]`. Then use the resulting hypothesis. Establish `hl2 : 0 < Real.log 2` using `Real.log_pos (by norm_num)`.

Establish `hlA : 0 ≤ Real.log (2 * A)` using `Real.log_nonneg (by linarith)`. Establish `h2 : Real.log (2 * A) ≤ Real.log (2 * A) / Real.log 2 * L`. Establish `hq : 0 ≤ Real.log (2 * A) / Real.log 2` using `div_nonneg hlA hl2.le`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[add_mul, one_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma log_le_of_le_exp_log_conductor {A M L : ℝ} (hA : 1 ≤ A) (hM : 1 ≤ M) (hL : Real.log 2 ≤ L) (hX : 0 < Real.exp L)
    (hML : M ≤ 2 * A * Real.exp L) :
    Real.log M ≤ (Real.log (2 * A) / Real.log 2 + 1) * L := by
  have hA2 : 0 < 2 * A := by linarith
  have h1 : Real.log M ≤ Real.log (2 * A) + L := by
    have h := Real.log_le_log (by linarith) hML
    rwa [Real.log_mul hA2.ne' (Real.exp_pos L).ne', Real.log_exp] at h
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlA : 0 ≤ Real.log (2 * A) := Real.log_nonneg (by linarith)
  have h2 : Real.log (2 * A) ≤ Real.log (2 * A) / Real.log 2 * L := by
    have hq : 0 ≤ Real.log (2 * A) / Real.log 2 := div_nonneg hlA hl2.le
    calc Real.log (2 * A) = Real.log (2 * A) / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ Real.log (2 * A) / Real.log 2 * L := mul_le_mul_of_nonneg_left hL hq
  rw [add_mul, one_mul]
  linarith

end Formalism.ZeroFreeDirichlet
