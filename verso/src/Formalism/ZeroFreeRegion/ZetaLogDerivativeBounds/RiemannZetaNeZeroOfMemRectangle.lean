import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

open Complex MeasureTheory

noncomputable section

namespace Formalism.ZF

/- English proof (translation)
Simplify using `only [Fy, norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hy]`.
-/
theorem norm_perronIntegrand (y : ℝ) (hy : 0 < y) (w : ℂ) :
    ‖Fy y w‖ = ‖deriv riemannZeta w / riemannZeta w‖ * y ^ w.re / (‖w‖ * ‖w - 1‖) := by
  simp only [Fy, norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hy]

/- English proof (translation)
Establish `h2 : (0:ℝ) < Real.log 2` using `Real.log_pos (by norm_num)`. Establish `hv0 : Real.log 2 ≤ Real.log (|v| + 2)` using `Real.log_le_log (by norm_num) (by linarith [abs_nonneg v])`. Establish `hvT : Real.log (|v| + 2) ≤ Real.log (T + 2)` using `Real.log_le_log (by linarith [abs_nonneg v]) (by linarith)`. Establish `hpos : 0 < Real.log (|v| + 2)` using `lt_of_lt_of_le h2 hv0`. Establish `e1 : c / Real.log (T + 2) ≤ c / Real.log (|v| + 2)` using `div_le_div_of_nonneg_left hc.le hpos hvT`.

Establish `e2 : c / Real.log (|v| + 2) ≤ c' / Real.log (|v| + 2)` using `div_le_div_of_nonneg_right hcc hpos.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_sub_div_log_le (c c' T v : ℝ) (hc : 0 < c) (hcc : c ≤ c') (hT : 0 ≤ T) (hv : |v| ≤ T) :
    1 - c' / Real.log (|v| + 2) ≤ 1 - c / Real.log (T + 2) := by
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hv0 : Real.log 2 ≤ Real.log (|v| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg v])
  have hvT : Real.log (|v| + 2) ≤ Real.log (T + 2) :=
    Real.log_le_log (by linarith [abs_nonneg v]) (by linarith)
  have hpos : 0 < Real.log (|v| + 2) := lt_of_lt_of_le h2 hv0
  have e1 : c / Real.log (T + 2) ≤ c / Real.log (|v| + 2) :=
    div_le_div_of_nonneg_left hc.le hpos hvT
  have e2 : c / Real.log (|v| + 2) ≤ c' / Real.log (|v| + 2) :=
    div_le_div_of_nonneg_right hcc hpos.le
  linarith

/- English proof (translation)
Introduce `w h1 _ h3 h4`. Conclude with `hZ w h4 ((one_sub_div_log_le c c₀ T w.im hc hcc hT h3).trans h1)`.
-/
theorem riemannZeta_ne_zero_of_mem_rectangle (c₀ : ℝ)
    (hZ : ∀ s : ℂ, s ≠ 1 → 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0)
    (c T σ₀ : ℝ) (hc : 0 < c) (hcc : c ≤ c₀) (hT : 0 ≤ T) :
    ∀ w : ℂ, 1 - c / Real.log (T + 2) ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T → w ≠ 1 →
      riemannZeta w ≠ 0 := by
  intro w h1 _ h3 h4
  exact hZ w h4 ((one_sub_div_log_le c c₀ T w.im hc hcc hT h3).trans h1)

/- English proof (translation)
Use `set w : ℂ := ((1 + 1 / Real.log y : ℝ) : ℂ) + t * I with hw`. Establish `hl : 0 < Real.log y` using `Real.log_pos hy`. Establish `hre : w.re = 1 + 1 / Real.log y` using `by simp [hw]`. Establish `him : w.im = t` using `by simp [hw]`. Establish `hy0 : 0 < y` using `by linarith`.

Rewrite using `[norm_perronIntegrand y hy0 w]`. Establish `hζ : ‖deriv riemannZeta w / riemannZeta w‖ ≤ Real.log y + C₂`. Use `hR w (by rw [hre]; have := one_div_pos.mpr hl; linarith)` as an intermediate fact. Rewrite `this` using `[hre]`. Simplify using `using this`.

Establish `hpow : y ^ w.re = Real.exp 1 * y`. Rewrite using `[hre, Real.rpow_add hy0, Real.rpow_one, Real.rpow_def_of_pos hy0, mul_one_div_cancel hl.ne']`. Expand and normalize the polynomial expressions, which then agree. Establish `ht0 : 0 < |t|` using `lt_of_lt_of_le hT ht`. Establish `hw1 : |t| ≤ ‖w‖` using `by rw [← him]; exact Complex.abs_im_le_norm w`.

Establish `hw2 : |t| ≤ ‖w - 1‖`. Establish `: (w - 1).im = t` using `by simp [him]`. Rewrite using `[← this]`. Conclude with `Complex.abs_im_le_norm _`. Establish `hden : t ^ 2 ≤ ‖w‖ * ‖w - 1‖`.

Rewrite using `[← sq_abs]`. Use polynomial arithmetic with `[abs_nonneg t]`. Establish `hnum : 0 ≤ Real.log y + C₂` using `le_trans (norm_nonneg _) hζ`. Rewrite using `[hpow]`. Establish `htp : 0 < t ^ 2` using `by rw [← sq_abs]; exact pow_pos ht0 2`.

Combine the equalities or inequalities in the displayed calculation. Apply `div_le_div_of_nonneg_left (mul_nonneg hnum (by positivity)) htp hden` to reduce the goal to its premises.
-/
theorem norm_perronIntegrand_le_right (C₂ : ℝ)
    (hR : ∀ s : ℂ, 1 < s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ 1 / (s.re - 1) + C₂)
    (y T t : ℝ) (hy : 1 < y) (hT : 0 < T) (ht : T ≤ |t|) :
    ‖Fy y (((1 + 1 / Real.log y : ℝ) : ℂ) + t * I)‖ ≤
      (Real.log y + C₂) * (Real.exp 1 * y) / t ^ 2 := by
  set w : ℂ := ((1 + 1 / Real.log y : ℝ) : ℂ) + t * I with hw
  have hl : 0 < Real.log y := Real.log_pos hy
  have hre : w.re = 1 + 1 / Real.log y := by simp [hw]
  have him : w.im = t := by simp [hw]
  have hy0 : 0 < y := by linarith
  rw [norm_perronIntegrand y hy0 w]
  have hζ : ‖deriv riemannZeta w / riemannZeta w‖ ≤ Real.log y + C₂ := by
    have := hR w (by rw [hre]; have := one_div_pos.mpr hl; linarith)
    rw [hre] at this
    simpa using this
  have hpow : y ^ w.re = Real.exp 1 * y := by
    rw [hre, Real.rpow_add hy0, Real.rpow_one, Real.rpow_def_of_pos hy0,
      mul_one_div_cancel hl.ne']
    ring
  have ht0 : 0 < |t| := lt_of_lt_of_le hT ht
  have hw1 : |t| ≤ ‖w‖ := by rw [← him]; exact Complex.abs_im_le_norm w
  have hw2 : |t| ≤ ‖w - 1‖ := by
    have : (w - 1).im = t := by simp [him]
    rw [← this]; exact Complex.abs_im_le_norm _
  have hden : t ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by
    rw [← sq_abs]; nlinarith [abs_nonneg t]
  have hnum : 0 ≤ Real.log y + C₂ := le_trans (norm_nonneg _) hζ
  rw [hpow]
  have htp : 0 < t ^ 2 := by rw [← sq_abs]; exact pow_pos ht0 2
  calc ‖deriv riemannZeta w / riemannZeta w‖ * (Real.exp 1 * y) / (‖w‖ * ‖w - 1‖)
      ≤ (Real.log y + C₂) * (Real.exp 1 * y) / (‖w‖ * ‖w - 1‖) := by
        gcongr
    _ ≤ (Real.log y + C₂) * (Real.exp 1 * y) / t ^ 2 := by
        apply div_le_div_of_nonneg_left (mul_nonneg hnum (by positivity)) htp hden

/- English proof (translation)
Use `set w : ℂ := (x : ℂ) + (v : ℂ) * I with hw`. Establish `hre : w.re = x` using `by simp [hw]`. Establish `him : w.im = v` using `by simp [hw]`. Establish `hy0 : 0 < y` using `by linarith`. Rewrite using `[norm_perronIntegrand y hy0 w]`.

Establish `hw1 : T ≤ ‖w‖` using `by rw [← hv, ← him]; exact Complex.abs_im_le_norm w`. Establish `hw2 : T ≤ ‖w - 1‖`. Establish `: (w - 1).im = v` using `by simp [him]`. Rewrite using `[← hv, ← this]`. Conclude with `Complex.abs_im_le_norm _`.

Establish `hne : w ≠ 1`. Introduce `h`. Establish `: (w - 1) = 0` using `by rw [h]; ring`. Rewrite `hw2` using `[this, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hreg : 1 - c₁ / Real.log (|w.im| + 2) ≤ w.re`. Rewrite using `[hre]`. Conclude with `(one_sub_div_log_le c c₁ T w.im hc hcc (by linarith) (by rw [him, hv])).trans hx1`. Establish `hD'` using `hD w hne hreg`. Rewrite `hD'` using `[him, hv]`.

Establish `hinv : ‖1 / (w - 1)‖ ≤ 1`. Rewrite using `[norm_div, norm_one]`. Conclude with `(div_le_one (by linarith)).mpr (by linarith)`. Establish `hζ : ‖deriv riemannZeta w / riemannZeta w‖ ≤ C₁ * Real.log (T + 2) ^ 2 + 1`. Combine the equalities or inequalities in the displayed calculation.

Establish `hpow : y ^ w.re ≤ y ^ σ₀`. Rewrite using `[hre]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hy hx2`. Establish `hden : T ^ 2 ≤ ‖w‖ * ‖w - 1‖` using `by nlinarith`. Establish `htp : 0 < T ^ 2` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Apply `div_le_div_of_nonneg_left (by positivity) htp hden` to reduce the goal to its premises.
-/
theorem norm_perronIntegrand_le_horizontal (c₁ C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hD : ∀ s : ℂ, s ≠ 1 → 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C₁ * Real.log (|s.im| + 2) ^ 2)
    (c y T x v σ₀ : ℝ) (hc : 0 < c) (hcc : c ≤ c₁) (hy : 1 ≤ y) (hT : 1 ≤ T) (hv : |v| = T)
    (hx1 : 1 - c / Real.log (T + 2) ≤ x) (hx2 : x ≤ σ₀) :
    ‖Fy y ((x : ℂ) + (v : ℂ) * I)‖ ≤
      (C₁ * Real.log (T + 2) ^ 2 + 1) * y ^ σ₀ / T ^ 2 := by
  set w : ℂ := (x : ℂ) + (v : ℂ) * I with hw
  have hre : w.re = x := by simp [hw]
  have him : w.im = v := by simp [hw]
  have hy0 : 0 < y := by linarith
  rw [norm_perronIntegrand y hy0 w]
  have hw1 : T ≤ ‖w‖ := by rw [← hv, ← him]; exact Complex.abs_im_le_norm w
  have hw2 : T ≤ ‖w - 1‖ := by
    have : (w - 1).im = v := by simp [him]
    rw [← hv, ← this]; exact Complex.abs_im_le_norm _
  have hne : w ≠ 1 := by
    intro h
    have : (w - 1) = 0 := by rw [h]; ring
    rw [this, norm_zero] at hw2; linarith
  have hreg : 1 - c₁ / Real.log (|w.im| + 2) ≤ w.re := by
    rw [hre]
    exact (one_sub_div_log_le c c₁ T w.im hc hcc (by linarith) (by rw [him, hv])).trans hx1
  have hD' := hD w hne hreg
  rw [him, hv] at hD'
  have hinv : ‖1 / (w - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith)).mpr (by linarith)
  have hζ : ‖deriv riemannZeta w / riemannZeta w‖ ≤ C₁ * Real.log (T + 2) ^ 2 + 1 := by
    calc ‖deriv riemannZeta w / riemannZeta w‖
        = ‖(deriv riemannZeta w / riemannZeta w + 1 / (w - 1)) - 1 / (w - 1)‖ := by ring_nf
      _ ≤ ‖deriv riemannZeta w / riemannZeta w + 1 / (w - 1)‖ + ‖1 / (w - 1)‖ := norm_sub_le _ _
      _ ≤ C₁ * Real.log (T + 2) ^ 2 + 1 := add_le_add hD' hinv
  have hpow : y ^ w.re ≤ y ^ σ₀ := by
    rw [hre]; exact Real.rpow_le_rpow_of_exponent_le hy hx2
  have hden : T ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by nlinarith
  have htp : 0 < T ^ 2 := by positivity
  calc ‖deriv riemannZeta w / riemannZeta w‖ * y ^ w.re / (‖w‖ * ‖w - 1‖)
      ≤ (C₁ * Real.log (T + 2) ^ 2 + 1) * y ^ σ₀ / (‖w‖ * ‖w - 1‖) := by
        gcongr
    _ ≤ (C₁ * Real.log (T + 2) ^ 2 + 1) * y ^ σ₀ / T ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) htp hden

/- English proof (translation)
Use `set L := Real.log (T + 2) with hLdef`. Establish `hL : 0 < L` using `Real.log_pos (by linarith)`. Use `set w : ℂ := (((1 - c / L : ℝ)) : ℂ) + u * I with hw`. Establish `hre : w.re = 1 - c / L` using `by simp [hw]`. Establish `him : w.im = u` using `by simp [hw]`.

Rewrite using `[norm_perronIntegrand y hy w]`. Establish `hcL : 0 < c / L` using `div_pos hc hL`. Establish `hw1 : 1 / 2 ≤ ‖w‖`. Use `Complex.abs_re_le_norm w` as an intermediate fact. Rewrite using `[hre, abs_of_pos (by linarith)] at this; linarith`.

Establish `hw2 : c / L ≤ ‖w - 1‖`. Establish `h` using `Complex.abs_re_le_norm (w - 1)`. Establish `: (w - 1).re = -(c / L)` using `by simp [hre]`. Rewrite `h` using `[this, abs_neg, abs_of_pos hcL]`. Conclude with `h`.

Establish `hne : w ≠ 1`. Introduce `h`. Establish `: (w - 1) = 0` using `by rw [h]; ring`. Rewrite `hw2` using `[this, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hreg : 1 - c₁ / Real.log (|w.im| + 2) ≤ w.re`. Rewrite using `[hre, him]`. Conclude with `one_sub_div_log_le c c₁ T u hc hcc hT hu`. Establish `hD'` using `hD w hne hreg`. Rewrite `hD'` using `[him]`.

Establish `hlogu : Real.log (|u| + 2) ^ 2 ≤ L ^ 2`. Establish `h0 : 0 ≤ Real.log (|u| + 2)` using `Real.log_nonneg (by linarith [abs_nonneg u])`. Establish `h1 : Real.log (|u| + 2) ≤ L` using `Real.log_le_log (by linarith [abs_nonneg u]) (by linarith)`. Conclude with `pow_le_pow_left₀ h0 h1 2`. Establish `hinv : ‖1 / (w - 1)‖ ≤ L / c`.

Rewrite using `[norm_div, norm_one]`. Establish `: 0 < ‖w - 1‖` using `lt_of_lt_of_le hcL hw2`. Rewrite using `[div_le_div_iff₀ this hc]`. Use `mul_le_mul_of_nonneg_left hw2 hL.le` as an intermediate fact. Rewrite `this` using `[mul_div_cancel₀ _ hL.ne']`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hζ : ‖deriv riemannZeta w / riemannZeta w‖ ≤ C₁ * L ^ 2 + L / c`. Combine the equalities or inequalities in the displayed calculation. Establish `hden : c / (2 * L) ≤ ‖w‖ * ‖w - 1‖`. Establish `: c / (2 * L) = (1 / 2) * (c / L)` using `by field_simp`.

Rewrite using `[this]`. Conclude with `mul_le_mul hw1 hw2 hcL.le (by linarith)`. Establish `hden0 : 0 < c / (2 * L)` using `by positivity`. Rewrite using `[hre]`. Combine the equalities or inequalities in the displayed calculation.

Apply `div_le_div_of_nonneg_left (by positivity) hden0 hden` to reduce the goal to its premises. Use `_ = (C₁ * L ^ 2 + L / c) * y ^ (1 - c / L) * (2 * L / c) := by`. Clear the denominators using the available nonvanishing facts.
-/
theorem norm_perronIntegrand_le_left (c₁ C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hD : ∀ s : ℂ, s ≠ 1 → 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C₁ * Real.log (|s.im| + 2) ^ 2)
    (c y T u : ℝ) (hc : 0 < c) (hcc : c ≤ c₁) (hy : 0 < y) (hT : 0 ≤ T) (hu : |u| ≤ T)
    (hhalf : 1 / 2 ≤ 1 - c / Real.log (T + 2)) :
    ‖Fy y (((1 - c / Real.log (T + 2) : ℝ) : ℂ) + u * I)‖ ≤
      (C₁ * Real.log (T + 2) ^ 2 + Real.log (T + 2) / c) * y ^ (1 - c / Real.log (T + 2)) *
        (2 * Real.log (T + 2) / c) := by
  set L := Real.log (T + 2) with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  set w : ℂ := (((1 - c / L : ℝ)) : ℂ) + u * I with hw
  have hre : w.re = 1 - c / L := by simp [hw]
  have him : w.im = u := by simp [hw]
  rw [norm_perronIntegrand y hy w]
  have hcL : 0 < c / L := div_pos hc hL
  have hw1 : 1 / 2 ≤ ‖w‖ := by
    have := Complex.abs_re_le_norm w
    rw [hre, abs_of_pos (by linarith)] at this; linarith
  have hw2 : c / L ≤ ‖w - 1‖ := by
    have h := Complex.abs_re_le_norm (w - 1)
    have : (w - 1).re = -(c / L) := by simp [hre]
    rw [this, abs_neg, abs_of_pos hcL] at h; exact h
  have hne : w ≠ 1 := by
    intro h
    have : (w - 1) = 0 := by rw [h]; ring
    rw [this, norm_zero] at hw2; linarith
  have hreg : 1 - c₁ / Real.log (|w.im| + 2) ≤ w.re := by
    rw [hre, him]
    exact one_sub_div_log_le c c₁ T u hc hcc hT hu
  have hD' := hD w hne hreg
  rw [him] at hD'
  have hlogu : Real.log (|u| + 2) ^ 2 ≤ L ^ 2 := by
    have h0 : 0 ≤ Real.log (|u| + 2) := Real.log_nonneg (by linarith [abs_nonneg u])
    have h1 : Real.log (|u| + 2) ≤ L := Real.log_le_log (by linarith [abs_nonneg u]) (by linarith)
    exact pow_le_pow_left₀ h0 h1 2
  have hinv : ‖1 / (w - 1)‖ ≤ L / c := by
    rw [norm_div, norm_one]
    have : 0 < ‖w - 1‖ := lt_of_lt_of_le hcL hw2
    rw [div_le_div_iff₀ this hc]
    have := mul_le_mul_of_nonneg_left hw2 hL.le
    rw [mul_div_cancel₀ _ hL.ne'] at this
    linarith
  have hζ : ‖deriv riemannZeta w / riemannZeta w‖ ≤ C₁ * L ^ 2 + L / c := by
    calc ‖deriv riemannZeta w / riemannZeta w‖
        = ‖(deriv riemannZeta w / riemannZeta w + 1 / (w - 1)) - 1 / (w - 1)‖ := by ring_nf
      _ ≤ ‖deriv riemannZeta w / riemannZeta w + 1 / (w - 1)‖ + ‖1 / (w - 1)‖ := norm_sub_le _ _
      _ ≤ C₁ * L ^ 2 + L / c := add_le_add (hD'.trans (mul_le_mul_of_nonneg_left hlogu hC₁)) hinv
  have hden : c / (2 * L) ≤ ‖w‖ * ‖w - 1‖ := by
    have : c / (2 * L) = (1 / 2) * (c / L) := by field_simp
    rw [this]
    exact mul_le_mul hw1 hw2 hcL.le (by linarith)
  have hden0 : 0 < c / (2 * L) := by positivity
  rw [hre]
  calc ‖deriv riemannZeta w / riemannZeta w‖ * y ^ (1 - c / L) / (‖w‖ * ‖w - 1‖)
      ≤ (C₁ * L ^ 2 + L / c) * y ^ (1 - c / L) / (‖w‖ * ‖w - 1‖) := by
        gcongr
    _ ≤ (C₁ * L ^ 2 + L / c) * y ^ (1 - c / L) / (c / (2 * L)) := by
        apply div_le_div_of_nonneg_left (by positivity) hden0 hden
    _ = (C₁ * L ^ 2 + L / c) * y ^ (1 - c / L) * (2 * L / c) := by
        field_simp

end Formalism.ZF
