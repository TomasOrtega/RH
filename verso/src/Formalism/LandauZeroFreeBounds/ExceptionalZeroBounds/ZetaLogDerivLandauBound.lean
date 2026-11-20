import Formalism.ZeroFreeRegion.LogDerivRegion

open Complex Filter Topology

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Rewrite using `[one_div, Complex.inv_re]`. Conclude with `div_nonneg h (Complex.normSq_nonneg w)`.
-/
lemma re_one_div_nonneg {w : ℂ} (h : 0 ≤ w.re) : 0 ≤ (1 / w).re := by
  rw [one_div, Complex.inv_re]
  exact div_nonneg h (Complex.normSq_nonneg w)

/- English proof (translation)
Rewrite using `[Complex.neg_re]`. Combine the linear relations using `[neg_le_abs x.re, Complex.abs_re_le_norm x]`.
-/
lemma neg_re_le_norm (x : ℂ) : (-x).re ≤ ‖x‖ := by
  rw [Complex.neg_re]
  linarith [neg_le_abs x.re, Complex.abs_re_le_norm x]

/- English proof (translation)
Establish `e : (k : ℂ) / w = ((k : ℝ) : ℂ) * (1 / w)` using `by push_cast; ring`. Rewrite using `[e, Complex.re_ofReal_mul]`. Conclude with `mul_nonneg (Nat.cast_nonneg k) (re_one_div_nonneg hw)`.
-/
private lemma re_natCast_div_nonneg (k : ℕ) {w : ℂ} (hw : 0 ≤ w.re) : 0 ≤ ((k : ℂ) / w).re := by
  have e : (k : ℂ) / w = ((k : ℝ) : ℂ) * (1 / w) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg (Nat.cast_nonneg k) (re_one_div_nonneg hw)

/- English proof (translation)
Establish `h1` using `Complex.abs_re_le_norm (z - (((11 / 10 : ℝ) : ℂ) + t * I))`. Establish `h2` using `Complex.abs_im_le_norm (z - (((11 / 10 : ℝ) : ℂ) + t * I))`. Establish `er : (z - (((11 / 10 : ℝ) : ℂ) + t * I)).re = z.re - 11 / 10` using `by simp`. Establish `ei : (z - (((11 / 10 : ℝ) : ℂ) + t * I)).im = z.im - t` using `by simp`. Rewrite `h1` using `[er]`.

Rewrite `h2` using `[ei]`. Establish `hre` using `abs_le.mp (h1.trans hz)`. Establish `h2'` using `h2.trans hz`. Establish `him1 : |t| - |z.im| ≤ |z.im - t|` using `by rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub t z.im`. Establish `him2 : |z.im| - |t| ≤ |z.im - t|` using `abs_sub_abs_le_abs_sub z.im t`.

Establish `hzre : 1 / 2 ≤ z.re` using `by linarith [hre.1]`. Establish `hz1 : z ≠ 1`. Introduce and unpack `rfl`. Simplify using `at h2'`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hd : 1 ≤ ‖z - 1‖`. Use `Complex.abs_im_le_norm (z - 1)` as an intermediate fact. Simplify using `only [Complex.sub_im, Complex.one_im, sub_zero] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hzn : ‖z‖ ≤ |t| + 3`.

Use `Complex.norm_le_abs_re_add_abs_im z` as an intermediate fact. Establish `hr : |z.re| ≤ 17 / 10` using `abs_le.mpr ⟨by linarith [hre.1], by linarith [hre.2]⟩`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg` using `Formalism.ZF.growthBound z (by linarith) hz1`. Establish `hA : 1 / ‖z - 1‖ ≤ 1` using `(div_le_one (by linarith)).mpr hd`.

Establish `hB : 1 / z.re ≤ 2` using `(div_le_iff₀ (by linarith)).mpr (by linarith)`. Establish `hC : ‖z‖ * (1 + 1 / z.re) ≤ (|t| + 3) * 3` using `mul_le_mul hzn (by linarith) (by have := one_div_pos.mpr (by linarith : (0 : ℝ) < z.re); linarith) (by positivity)`. Use `⟨hzre, hz1, ?_⟩` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma re_ge_and_norm_zeta_le_of_near_eleven_tenths {t : ℝ} (ht : 2 < |t|) {z : ℂ}
    (hz : ‖z - (((11 / 10 : ℝ) : ℂ) + t * I)‖ ≤ 3 / 5) :
    1 / 2 ≤ z.re ∧ z ≠ 1 ∧ ‖riemannZeta z‖ ≤ 6 * (|t| + 2) := by
  have h1 := Complex.abs_re_le_norm (z - (((11 / 10 : ℝ) : ℂ) + t * I))
  have h2 := Complex.abs_im_le_norm (z - (((11 / 10 : ℝ) : ℂ) + t * I))
  have er : (z - (((11 / 10 : ℝ) : ℂ) + t * I)).re = z.re - 11 / 10 := by simp
  have ei : (z - (((11 / 10 : ℝ) : ℂ) + t * I)).im = z.im - t := by simp
  rw [er] at h1
  rw [ei] at h2
  have hre := abs_le.mp (h1.trans hz)
  have h2' := h2.trans hz
  have him1 : |t| - |z.im| ≤ |z.im - t| := by rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub t z.im
  have him2 : |z.im| - |t| ≤ |z.im - t| := abs_sub_abs_le_abs_sub z.im t
  have hzre : 1 / 2 ≤ z.re := by linarith [hre.1]
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at h2'
    linarith
  have hd : 1 ≤ ‖z - 1‖ := by
    have := Complex.abs_im_le_norm (z - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
    linarith
  have hzn : ‖z‖ ≤ |t| + 3 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    have hr : |z.re| ≤ 17 / 10 := abs_le.mpr ⟨by linarith [hre.1], by linarith [hre.2]⟩
    linarith
  have hg := Formalism.ZF.growthBound z (by linarith) hz1
  have hA : 1 / ‖z - 1‖ ≤ 1 := (div_le_one (by linarith)).mpr hd
  have hB : 1 / z.re ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hC : ‖z‖ * (1 + 1 / z.re) ≤ (|t| + 3) * 3 :=
    mul_le_mul hzn (by linarith)
      (by have := one_div_pos.mpr (by linarith : (0 : ℝ) < z.re); linarith) (by positivity)
  refine ⟨hzre, hz1, ?_⟩
  linarith

/- English proof (translation)
Establish `hz0re : ((((11 / 10 : ℝ) : ℂ) + t * I)).re = 11 / 10` using `by simp`. Establish `hinv` using `Formalism.ZF.zetaInvBound_statement (((11 / 10 : ℝ) : ℂ) + t * I) (by rw [hz0re]; norm_num)`. Establish `h1110 : (11 / 10 : ℝ) / (11 / 10 - 1) = 11` using `by norm_num`. Rewrite `hinv` using `[hz0re, h1110]`. Establish `hz0ne : riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I) ≠ 0` using `riemannZeta_ne_zero_of_one_lt_re (by rw [hz0re]; norm_num)`.

Establish `hpos : 0 < ‖riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I)‖` using `norm_pos_iff.mpr hz0ne`. Establish `h11 : 1 ≤ ‖riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I)‖ * 11`. Use `mul_le_mul_of_nonneg_left hinv hpos.le` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ hpos.ne']`. Then use the resulting hypothesis. Establish `hT : 4 ≤ |t| + 2` using `by linarith`.

Establish `hM1 : (1 : ℝ) ≤ 66 * (|t| + 2)` using `by linarith`. Take `⟨Z, m, hZ, -, -, hbound⟩` from `Formalism.ZF.landauLocal riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I) (3 / 5) (66 * (|t| + 2)) (by norm_num) hM1 (fun z hz => (differentiableAt_riemannZeta (re_ge_and_norm_zeta_le_of_near_eleven_tenths ht (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz)).2.1).differentiableWithi …`. Establish `hb` using `(re_ge_and_norm_zeta_le_of_near_eleven_tenths ht (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz)).2.2`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h11 (by linarith : (0 : ℝ) ≤ 6 * (|t| + 2))])`. Establish `hzmem : ((σ : ℂ) + t * I) ∈ Metric.closedBall (((11 / 10 : ℝ) : ℂ) + t * I) (3 / 5 / 6)`.

Rewrite using `[Metric.mem_closedBall, dist_eq_norm]`. Establish `e : (σ : ℂ) + t * I - (((11 / 10 : ℝ) : ℂ) + t * I) = ((σ - 11 / 10 : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[e, Complex.norm_real, Real.norm_eq_abs, abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Establish `hzre : ((σ : ℂ) + t * I).re = σ` using `by simp`.

Establish `hzne : riemannZeta ((σ : ℂ) + t * I) ≠ 0` using `riemannZeta_ne_zero_of_one_lt_re (by rw [hzre]; exact hσ)`. Establish `hb` using `hbound _ hzmem hzne`. Establish `hsum : 0 ≤ (∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ)).re`. Rewrite using `[Complex.re_sum]`. Apply `Finset.sum_nonneg` to reduce the goal to its premises.

Introduce `ρ hρ`. Establish `hρ0` using `((hZ ρ).mp hρ).2`. Establish `hρre : ρ.re ≤ 1`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `riemannZeta_ne_zero_of_one_lt_re h hρ0`. Apply `re_natCast_div_nonneg` to reduce the goal to its premises. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hneg` using `neg_re_le_norm (deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I) - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ))`.

Establish `hsplit : (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I))).re = (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I) - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ))).re - (∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ)).re`. Simplify using `only [Complex.neg_re, Complex.sub_re]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlogM : Real.log (66 * (|t| + 2)) ≤ 7 * Real.log (|t| + 2)`. Establish `h6 : (4 : ℝ) ^ 6 ≤ (|t| + 2) ^ 6` using `pow_le_pow_left₀ (by norm_num) hT 6`.

Establish `hle : 66 * (|t| + 2) ≤ (|t| + 2) ^ 7`. Establish `e7 : (|t| + 2) ^ 7 = (|t| + 2) ^ 6 * (|t| + 2)` using `by ring`. Rewrite using `[e7]`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.

Establish `h72 : 72 * Real.log (66 * (|t| + 2)) / (3 / 5) = 120 * Real.log (66 * (|t| + 2))` using `by ring`. Rewrite using `[hsplit]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma zeta_log_deriv_landau_bound (t σ : ℝ) (ht : 2 < |t|) (hσ : 1 < σ) (hσ' : σ ≤ 6 / 5) :
    (-(deriv riemannZeta ((σ:ℂ) + t * I) / riemannZeta ((σ:ℂ) + t * I))).re ≤
      840 * Real.log (|t| + 2) := by
  have hz0re : ((((11 / 10 : ℝ) : ℂ) + t * I)).re = 11 / 10 := by simp
  have hinv := Formalism.ZF.zetaInvBound_statement (((11 / 10 : ℝ) : ℂ) + t * I) (by rw [hz0re]; norm_num)
  have h1110 : (11 / 10 : ℝ) / (11 / 10 - 1) = 11 := by norm_num
  rw [hz0re, h1110] at hinv
  have hz0ne : riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hz0re]; norm_num)
  have hpos : 0 < ‖riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I)‖ := norm_pos_iff.mpr hz0ne
  have h11 : 1 ≤ ‖riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I)‖ * 11 := by
    have := mul_le_mul_of_nonneg_left hinv hpos.le
    rwa [mul_inv_cancel₀ hpos.ne'] at this
  have hT : 4 ≤ |t| + 2 := by linarith
  have hM1 : (1 : ℝ) ≤ 66 * (|t| + 2) := by linarith
  obtain ⟨Z, m, hZ, -, -, hbound⟩ := Formalism.ZF.landauLocal riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I) (3 / 5)
    (66 * (|t| + 2)) (by norm_num) hM1
    (fun z hz => (differentiableAt_riemannZeta
      (re_ge_and_norm_zeta_le_of_near_eleven_tenths ht (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz)).2.1).differentiableWithinAt)
    hz0ne
    (fun z hz => by
      have hb := (re_ge_and_norm_zeta_le_of_near_eleven_tenths ht (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz)).2.2
      nlinarith [mul_le_mul_of_nonneg_left h11 (by linarith : (0 : ℝ) ≤ 6 * (|t| + 2))])
  have hzmem : ((σ : ℂ) + t * I) ∈ Metric.closedBall (((11 / 10 : ℝ) : ℂ) + t * I) (3 / 5 / 6) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have e : (σ : ℂ) + t * I - (((11 / 10 : ℝ) : ℂ) + t * I) = ((σ - 11 / 10 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hzre : ((σ : ℂ) + t * I).re = σ := by simp
  have hzne : riemannZeta ((σ : ℂ) + t * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hzre]; exact hσ)
  have hb := hbound _ hzmem hzne
  have hsum : 0 ≤ (∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_nonneg
    intro ρ hρ
    have hρ0 := ((hZ ρ).mp hρ).2
    have hρre : ρ.re ≤ 1 := by
      by_contra h
      push_neg at h
      exact riemannZeta_ne_zero_of_one_lt_re h hρ0
    apply re_natCast_div_nonneg
    simp
    linarith
  have hneg := neg_re_le_norm (deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I) -
      ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ))
  have hsplit : (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I))).re =
      (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I) -
        ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ))).re -
        (∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ)).re := by
    simp only [Complex.neg_re, Complex.sub_re]; ring
  have hlogM : Real.log (66 * (|t| + 2)) ≤ 7 * Real.log (|t| + 2) := by
    have h6 : (4 : ℝ) ^ 6 ≤ (|t| + 2) ^ 6 := pow_le_pow_left₀ (by norm_num) hT 6
    have hle : 66 * (|t| + 2) ≤ (|t| + 2) ^ 7 := by
      have e7 : (|t| + 2) ^ 7 = (|t| + 2) ^ 6 * (|t| + 2) := by ring
      rw [e7]; nlinarith
    calc Real.log (66 * (|t| + 2)) ≤ Real.log ((|t| + 2) ^ 7) := Real.log_le_log (by linarith) hle
      _ = 7 * Real.log (|t| + 2) := by rw [Real.log_pow]; norm_num
  have h72 : 72 * Real.log (66 * (|t| + 2)) / (3 / 5) = 120 * Real.log (66 * (|t| + 2)) := by ring
  rw [hsplit]
  linarith

/- English proof (translation)
Take `⟨c, C, hc, hreg⟩` from `Formalism.ZF.logDerivRegion`. Take `⟨K₃, hK₃⟩ : ∃ k : ℝ, k = ∑' n, ‖LSeries.term (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((6 / 5 : ℝ) : ℂ) n‖` from `⟨_, rfl⟩`. Establish `hlog4 : 0 ≤ Real.log 4` using `Real.log_nonneg (by norm_num)`. Use `⟨840 + |C| * Real.log 4 + |K₃|, add_nonneg (add_nonneg (by norm_num) (mul_nonneg (abs_nonneg _) hlog4)) (abs_nonneg _), ?_⟩` and prove the remaining obligations. Introduce `σ t hσ hσ2`.

Establish `hre1 : 0 ≤ ((σ : ℂ) - 1 + t * I).re` using `by simp; linarith`. Establish `hR` using `re_one_div_nonneg hre1`. Establish `hL0 : 0 ≤ Real.log (|t| + 2)` using `Real.log_nonneg (by linarith [abs_nonneg t])`. Establish `hC0 : 0 ≤ |C| * Real.log 4 * Real.log (|t| + 2)` using `mul_nonneg (mul_nonneg (abs_nonneg _) hlog4) hL0`. Establish `hK30 : 0 ≤ |K₃| * Real.log (|t| + 2)` using `mul_nonneg (abs_nonneg _) hL0`.

Establish `h840 : 0 ≤ 840 * Real.log (|t| + 2)` using `mul_nonneg (by norm_num) hL0`. Break down `le_or_gt |t| 2 with ht | ht` into its components or cases. Establish `hs1 : ((σ : ℂ) + t * I) ≠ 1`. Introduce `h`. Use `congrArg Complex.re h` as an intermediate fact.

Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `him : ((σ : ℂ) + t * I).im = t` using `by simp`. Establish `hsre : ((σ : ℂ) + t * I).re = σ` using `by simp`. Establish `hLpos : 0 < Real.log (|t| + 2)` using `Real.log_pos (by linarith [abs_nonneg t])`.

Establish `hcond : 1 - c / Real.log (|((σ : ℂ) + t * I).im| + 2) ≤ ((σ : ℂ) + t * I).re`. Rewrite using `[him, hsre]`. Use `div_nonneg hc.le hLpos.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb` using `hreg _ hs1 hcond`.

Rewrite `hb` using `[him]`. Establish `es : (σ : ℂ) + t * I - 1 = (σ : ℂ) - 1 + t * I` using `by ring`. Rewrite `hb` using `[es]`. Establish `hneg` using `neg_re_le_norm (deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I) + 1 / ((σ : ℂ) - 1 + t * I))`. Establish `hsplit : (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I))).re = (1 / ((σ : ℂ) - 1 + t * I)).re + (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I) + 1 / ((σ : ℂ) - 1 + t * I))).re`.

Simplify using `only [Complex.neg_re, Complex.add_re]`. Expand and normalize the polynomial expressions, which then agree. Establish `hL4 : Real.log (|t| + 2) ≤ Real.log 4` using `Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)`. Establish `hCL : C * Real.log (|t| + 2) ^ 2 ≤ |C| * Real.log 4 * Real.log (|t| + 2)`. Establish `h1 : C * Real.log (|t| + 2) ^ 2 ≤ |C| * Real.log (|t| + 2) ^ 2` using `mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)`.

Establish `h2 : |C| * (Real.log (|t| + 2) * Real.log (|t| + 2)) ≤ |C| * (Real.log 4 * Real.log (|t| + 2))` using `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL4 hL0) (abs_nonneg C)`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hsplit]`. Use the polynomial consequences of the given equalities and inequalities. Break down `le_or_gt σ (6 / 5) with hσ' | hσ'` into its components or cases.

Use `zeta_log_deriv_landau_bound t σ ht hσ hσ'` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hs1 : 1 < ((σ : ℂ) + t * I).re` using `by simp; linarith`. Establish `hLs` using `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1`. Rewrite `hLs` using `[neg_div]`.

Rewrite using `[← hLs]`. Establish `hsum` using `ArithmeticFunction.LSeriesSummable_vonMangoldt hs1`. Establish `hsum0` using `ArithmeticFunction.LSeriesSummable_vonMangoldt (s := ((6 / 5 : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; norm_num)`. Establish `hbd : (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I)).re ≤ K₃`. Combine the equalities or inequalities in the displayed calculation.

Establish `hL1 : 1 ≤ Real.log (|t| + 2)`. Rewrite using `[Real.le_log_iff_exp_le (by linarith [abs_nonneg t])]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Evaluate the numerical expressions using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hK3 : K₃ ≤ |K₃| * Real.log (|t| + 2)`. Use `mul_le_mul_of_nonneg_left hL1 (abs_nonneg K₃)` as an intermediate fact. Combine the linear relations using `[le_abs_self K₃]`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma zeta_neg_log_deriv_re_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
    (-(deriv riemannZeta ((σ:ℂ) + t * I) / riemannZeta ((σ:ℂ) + t * I))).re ≤
      (1 / ((σ : ℂ) - 1 + t * I)).re + K * Real.log (|t| + 2) := by
  obtain ⟨c, C, hc, hreg⟩ := Formalism.ZF.logDerivRegion
  obtain ⟨K₃, hK₃⟩ : ∃ k : ℝ, k = ∑' n, ‖LSeries.term (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      ((6 / 5 : ℝ) : ℂ) n‖ := ⟨_, rfl⟩
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨840 + |C| * Real.log 4 + |K₃|,
    add_nonneg (add_nonneg (by norm_num) (mul_nonneg (abs_nonneg _) hlog4)) (abs_nonneg _), ?_⟩
  intro σ t hσ hσ2
  have hre1 : 0 ≤ ((σ : ℂ) - 1 + t * I).re := by simp; linarith
  have hR := re_one_div_nonneg hre1
  have hL0 : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hC0 : 0 ≤ |C| * Real.log 4 * Real.log (|t| + 2) := mul_nonneg (mul_nonneg (abs_nonneg _) hlog4) hL0
  have hK30 : 0 ≤ |K₃| * Real.log (|t| + 2) := mul_nonneg (abs_nonneg _) hL0
  have h840 : 0 ≤ 840 * Real.log (|t| + 2) := mul_nonneg (by norm_num) hL0
  rcases le_or_gt |t| 2 with ht | ht
  ·
    have hs1 : ((σ : ℂ) + t * I) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have him : ((σ : ℂ) + t * I).im = t := by simp
    have hsre : ((σ : ℂ) + t * I).re = σ := by simp
    have hLpos : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
    have hcond : 1 - c / Real.log (|((σ : ℂ) + t * I).im| + 2) ≤ ((σ : ℂ) + t * I).re := by
      rw [him, hsre]; have := div_nonneg hc.le hLpos.le; linarith
    have hb := hreg _ hs1 hcond
    rw [him] at hb
    have es : (σ : ℂ) + t * I - 1 = (σ : ℂ) - 1 + t * I := by ring
    rw [es] at hb
    have hneg := neg_re_le_norm (deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I) +
      1 / ((σ : ℂ) - 1 + t * I))
    have hsplit : (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I))).re =
        (1 / ((σ : ℂ) - 1 + t * I)).re + (-(deriv riemannZeta ((σ : ℂ) + t * I) /
          riemannZeta ((σ : ℂ) + t * I) + 1 / ((σ : ℂ) - 1 + t * I))).re := by
      simp only [Complex.neg_re, Complex.add_re]; ring
    have hL4 : Real.log (|t| + 2) ≤ Real.log 4 :=
      Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
    have hCL : C * Real.log (|t| + 2) ^ 2 ≤ |C| * Real.log 4 * Real.log (|t| + 2) := by
      have h1 : C * Real.log (|t| + 2) ^ 2 ≤ |C| * Real.log (|t| + 2) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)
      have h2 : |C| * (Real.log (|t| + 2) * Real.log (|t| + 2)) ≤ |C| * (Real.log 4 * Real.log (|t| + 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL4 hL0) (abs_nonneg C)
      nlinarith
    rw [hsplit]
    nlinarith
  rcases le_or_gt σ (6 / 5) with hσ' | hσ'
  ·
    have := zeta_log_deriv_landau_bound t σ ht hσ hσ'
    nlinarith
  ·
    have hs1 : 1 < ((σ : ℂ) + t * I).re := by simp; linarith
    have hLs := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1
    rw [neg_div] at hLs
    rw [← hLs]
    have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hs1
    have hsum0 := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := ((6 / 5 : ℝ) : ℂ))
      (by rw [Complex.ofReal_re]; norm_num)
    have hbd : (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I)).re ≤ K₃ := by
      calc (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I)).re
          ≤ ‖LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I)‖ :=
            Complex.re_le_norm _
        _ ≤ ∑' n, ‖LSeries.term (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I) n‖ :=
            norm_tsum_le_tsum_norm (summable_norm_iff.mpr hsum)
        _ ≤ ∑' n, ‖LSeries.term (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((6 / 5 : ℝ) : ℂ) n‖ :=
            Summable.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re _ (by simp; linarith) n)
              (summable_norm_iff.mpr hsum) (summable_norm_iff.mpr hsum0)
        _ = K₃ := hK₃.symm
    have hL1 : 1 ≤ Real.log (|t| + 2) := by
      rw [Real.le_log_iff_exp_le (by linarith [abs_nonneg t])]
      have := Real.exp_one_lt_d9; norm_num at this; linarith
    have hK3 : K₃ ≤ |K₃| * Real.log (|t| + 2) := by
      have := mul_le_mul_of_nonneg_left hL1 (abs_nonneg K₃)
      linarith [le_abs_self K₃]
    nlinarith

end Formalism.ZeroFreeDirichlet
