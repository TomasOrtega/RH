import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.OdeRoots.Above

/- English proof (translation)
Establish `h1 : inner ℝ x (z * x + y) = z.re * ‖x‖ ^ 2 + inner ℝ x y`. Rewrite using `[inner_add_right]`. Use `congr 1`. Rewrite using `[Complex.inner, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]`. Simplify using `only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : -(‖x‖ * ‖y‖) ≤ inner ℝ x y` using `(abs_le.1 (abs_real_inner_le_norm x y)).1`. Rewrite using `[h1]`. Use `set p := ‖x‖`. Use `set q := ‖y‖`.

Establish `h3 : 0 ≤ (d * p - q) ^ 2 / d` using `by positivity`. Establish `h4 : (d * p - q) ^ 2 / d = d * p ^ 2 - 2 * (p * q) + (1 / d) * q ^ 2`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h5 : (2 * (z.re - s) - d) * p ^ 2 - (1 / d) * q ^ 2 ≤ 2 * (z.re * p ^ 2 + inner ℝ x y) + p ^ 2 * (-2 * s)`.

Use the polynomial consequences of the given equalities and inequalities. Use `mul_le_mul_of_nonneg_right h5 he` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem energy_lower (z x y : ℂ) (s d e : ℝ) (hd : 0 < d) (he : 0 ≤ e) :
    (2 * (z.re - s) - d) * (‖x‖ ^ 2 * e) - (1 / d) * (‖y‖ ^ 2 * e) ≤
      2 * (inner ℝ x (z * x + y)) * e + ‖x‖ ^ 2 * (e * (-2 * s)) := by
  have h1 : inner ℝ x (z * x + y) = z.re * ‖x‖ ^ 2 + inner ℝ x y := by
    rw [inner_add_right]
    congr 1
    rw [Complex.inner, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have h2 : -(‖x‖ * ‖y‖) ≤ inner ℝ x y := (abs_le.1 (abs_real_inner_le_norm x y)).1
  rw [h1]
  set p := ‖x‖
  set q := ‖y‖
  have h3 : 0 ≤ (d * p - q) ^ 2 / d := by positivity
  have h4 : (d * p - q) ^ 2 / d = d * p ^ 2 - 2 * (p * q) + (1 / d) * q ^ 2 := by
    field_simp
    ring
  have h5 : (2 * (z.re - s) - d) * p ^ 2 - (1 / d) * q ^ 2 ≤
      2 * (z.re * p ^ 2 + inner ℝ x y) + p ^ 2 * (-2 * s) := by
    nlinarith
  have := mul_le_mul_of_nonneg_right h5 he
  nlinarith

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `h1 : (∫⁻ _t in Ioi T₀, ENNReal.ofReal ε) ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (W t)`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : (∫⁻ _t in Ioi T₀, ENNReal.ofReal ε) = ⊤`.

Rewrite using `[setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top]`. Simplify using `using hε`. Rewrite `h1` using `[h2]`. Conclude with `absurd (lt_of_le_of_lt h1 hW) (lt_irrefl _)`.
-/
theorem exists_small_of_lintegral (W : ℝ → ℝ)
    (hW : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (W t)) < ⊤) (T₀ : ℝ) (hT₀ : 0 ≤ T₀)
    (ε : ℝ) (hε : 0 < ε) : ∃ T, T₀ ≤ T ∧ W T < ε := by
  by_contra hcon
  push_neg at hcon
  have h1 : (∫⁻ _t in Ioi T₀, ENNReal.ofReal ε) ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (W t) := by
    calc (∫⁻ _t in Ioi T₀, ENNReal.ofReal ε)
        ≤ ∫⁻ t in Ioi T₀, ENNReal.ofReal (W t) :=
          setLIntegral_mono' measurableSet_Ioi fun t ht =>
            ENNReal.ofReal_le_ofReal (hcon t (le_of_lt ht))
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (W t) :=
          lintegral_mono_set (Ioi_subset_Ioi hT₀)
  have h2 : (∫⁻ _t in Ioi T₀, ENNReal.ofReal ε) = ⊤ := by
    rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top]
    simpa using hε
  rw [h2] at h1
  exact absurd (lt_of_le_of_lt h1 hW) (lt_irrefl _)

/- English proof (translation)
Set `B : ℝ → ℝ` to `fun r => -(Real.exp (a * t) * Real.exp (-2 * a * r)) / (4 * a)`. Set `B' : ℝ → ℝ` to `fun r => Real.exp (a * t) * Real.exp (-2 * a * r) / 2`. Establish `hB' : Continuous B'` using `by fun_prop`. Establish `hBd : ∀ r, HasDerivAt B (B' r) r`. Introduce `r`.

Establish `h1 : HasDerivAt (fun r : ℝ => Real.exp (-2 * a * r)) (Real.exp (-2 * a * r) * (-2 * a)) r`. Simplify using `using ((hasDerivAt_id r).const_mul (-2 * a)).exp`. Establish `h2` using `((h1.const_mul (Real.exp (a * t))).neg).div_const (4 * a)`. Use `h2.congr_deriv ?_` and prove the remaining obligations. Simplify using `only [B']`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hI : ∫ r in t..T, B' r = B T - B t` using `intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hBd r) (hB'.intervalIntegrable _ _)`. Establish `hpt : ∀ r, Real.exp (-a * r) * x r ≤ (Real.exp (-a * t) / 2) * x r ^ 2 + B' r`. Introduce `r`.

Take `⟨u, hu⟩ : ∃ u, u = Real.exp (-a * t)` from `⟨_, rfl⟩`. Take `⟨v, hv⟩ : ∃ v, v = Real.exp (a * t)` from `⟨_, rfl⟩`. Take `⟨w, hw⟩ : ∃ w, w = Real.exp (-a * r)` from `⟨_, rfl⟩`. Establish `huv : u * v = 1`. Rewrite using `[hu, hv, ← Real.exp_add]`.

Simplify using the standard rewrite rules. Establish `hv0 : 0 < v` using `hv ▸ Real.exp_pos _`. Establish `hw2 : Real.exp (-2 * a * r) = w ^ 2`. Rewrite using `[hw, sq, ← Real.exp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [B']`. Rewrite using `[hw2, ← hu, ← hv, ← hw]`. Establish `h0 : 0 ≤ v * (u * x r - w) ^ 2 / 2` using `by positivity`. Establish `h1 : v * (u * x r - w) ^ 2 / 2 = (u * v) * u * x r ^ 2 / 2 - (u * v) * (x r * w) + v * w ^ 2 / 2` using `by ring`.

Rewrite `h0` using `[h1, huv]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hmono : ∫ r in t..T, Real.exp (-a * r) * x r ≤ ∫ r in t..T, ((Real.exp (-a * t) / 2) * x r ^ 2 + B' r)` using `intervalIntegral.integral_mono_on hT (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop) (fun r _ => hpt r)`. Establish `hsplit : ∫ r in t..T, ((Real.exp (-a * t) / 2) * x r ^ 2 + B' r) = (Real.exp (-a * t) / 2) * (∫ r in t..T, x r ^ 2) + (B T - B t)`. Establish `c1 : IntervalIntegrable (fun r => (Real.exp (-a * t) / 2) * x r ^ 2) volume t T`.

Apply `Continuous.intervalIntegrable` to reduce the goal to its premises. Use `fun_prop`. Rewrite using `[intervalIntegral.integral_add c1 (hB'.intervalIntegrable _ _), intervalIntegral.integral_const_mul, hI]`. Establish `hBT : B T ≤ 0`. Simplify using `only [B]`.

Establish `: 0 ≤ Real.exp (a * t) * Real.exp (-2 * a * T) / (4 * a)` using `by positivity`. Rewrite using `[neg_div]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hBt : -B t = Real.exp (-a * t) * (1 / (4 * a))`. Simplify using `only [B]`.

Establish `e : Real.exp (a * t) * Real.exp (-2 * a * t) = Real.exp (-a * t)`. Rewrite using `[← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hCe : (Real.exp (-a * t) / 2) * (∫ r in t..T, x r ^ 2) ≤ (Real.exp (-a * t) / 2) * C` using `mul_le_mul_of_nonneg_left hC (by positivity)`. Rewrite `hmono` using `[hsplit]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem young_tail (a C : ℝ) (ha : 0 < a) (x : ℝ → ℝ) (hx : Continuous x) (t T : ℝ) (hT : t ≤ T)
    (hC : ∫ r in t..T, x r ^ 2 ≤ C) :
    ∫ r in t..T, Real.exp (-a * r) * x r ≤ Real.exp (-a * t) * (C / 2 + 1 / (4 * a)) := by
  let B : ℝ → ℝ := fun r => -(Real.exp (a * t) * Real.exp (-2 * a * r)) / (4 * a)
  let B' : ℝ → ℝ := fun r => Real.exp (a * t) * Real.exp (-2 * a * r) / 2
  have hB' : Continuous B' := by fun_prop
  have hBd : ∀ r, HasDerivAt B (B' r) r := by
    intro r
    have h1 : HasDerivAt (fun r : ℝ => Real.exp (-2 * a * r))
        (Real.exp (-2 * a * r) * (-2 * a)) r := by
      simpa using ((hasDerivAt_id r).const_mul (-2 * a)).exp
    have h2 := ((h1.const_mul (Real.exp (a * t))).neg).div_const (4 * a)
    refine h2.congr_deriv ?_
    simp only [B']
    field_simp
    ring
  have hI : ∫ r in t..T, B' r = B T - B t :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hBd r)
      (hB'.intervalIntegrable _ _)
  have hpt : ∀ r, Real.exp (-a * r) * x r ≤ (Real.exp (-a * t) / 2) * x r ^ 2 + B' r := by
    intro r
    obtain ⟨u, hu⟩ : ∃ u, u = Real.exp (-a * t) := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v, v = Real.exp (a * t) := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w, w = Real.exp (-a * r) := ⟨_, rfl⟩
    have huv : u * v = 1 := by
      rw [hu, hv, ← Real.exp_add]
      simp
    have hv0 : 0 < v := hv ▸ Real.exp_pos _
    have hw2 : Real.exp (-2 * a * r) = w ^ 2 := by
      rw [hw, sq, ← Real.exp_add]
      congr 1
      ring
    simp only [B']
    rw [hw2, ← hu, ← hv, ← hw]
    have h0 : 0 ≤ v * (u * x r - w) ^ 2 / 2 := by positivity
    have h1 : v * (u * x r - w) ^ 2 / 2 =
        (u * v) * u * x r ^ 2 / 2 - (u * v) * (x r * w) + v * w ^ 2 / 2 := by ring
    rw [h1, huv] at h0
    nlinarith
  have hmono : ∫ r in t..T, Real.exp (-a * r) * x r ≤
      ∫ r in t..T, ((Real.exp (-a * t) / 2) * x r ^ 2 + B' r) :=
    intervalIntegral.integral_mono_on hT (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop) (fun r _ => hpt r)
  have hsplit : ∫ r in t..T, ((Real.exp (-a * t) / 2) * x r ^ 2 + B' r) =
      (Real.exp (-a * t) / 2) * (∫ r in t..T, x r ^ 2) + (B T - B t) := by
    have c1 : IntervalIntegrable (fun r => (Real.exp (-a * t) / 2) * x r ^ 2) volume t T := by
      apply Continuous.intervalIntegrable; fun_prop
    rw [intervalIntegral.integral_add c1 (hB'.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, hI]
  have hBT : B T ≤ 0 := by
    simp only [B]
    have : 0 ≤ Real.exp (a * t) * Real.exp (-2 * a * T) / (4 * a) := by positivity
    rw [neg_div]
    linarith
  have hBt : -B t = Real.exp (-a * t) * (1 / (4 * a)) := by
    simp only [B]
    have e : Real.exp (a * t) * Real.exp (-2 * a * t) = Real.exp (-a * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e]
    ring
  have hCe : (Real.exp (-a * t) / 2) * (∫ r in t..T, x r ^ 2) ≤ (Real.exp (-a * t) / 2) * C :=
    mul_le_mul_of_nonneg_left hC (by positivity)
  rw [hsplit] at hmono
  nlinarith

/- English proof (translation)
Introduce `z s s' hs hs' f g hf hg hgi hfi`. Take `⟨a, hadef⟩ : ∃ a : ℝ, a = z.re - s` from `⟨_, rfl⟩`. Establish `ha : 0 < a` using `by rw [hadef]; exact sub_pos.2 hs`. Set `ft : ℝ → ℂ` to `fun t => f (max t 0)`. Establish `hfon : ContinuousOn f (Ici 0)` using `fun t ht => (hf t ht).continuousAt.continuousWithinAt`.

Establish `hft : Continuous ft` using `hfon.comp_continuous (continuous_id.max continuous_const) (fun t => mem_Ici.2 (le_max_right _ _))`. Establish `hfe : ∀ t, 0 ≤ t → ft t = f t` using `fun t ht => by simp [ft, max_eq_left ht]`. Set `E : ℝ → ℝ` to `fun t => Real.exp (-2 * s * t)`. Establish `hE : Continuous E` using `by fun_prop`. Establish `hEpos : ∀ t, 0 ≤ E t` using `fun t => (Real.exp_pos _).le`.

Set `U : ℝ → ℝ` to `fun t => ‖ft t‖ ^ 2 * E t`. Set `V : ℝ → ℝ` to `fun t => ‖g t‖ ^ 2 * E t`. Establish `hU : Continuous U` using `by fun_prop`. Establish `hV : Continuous V` using `by fun_prop`. Establish `hUn : ∀ t, 0 ≤ U t` using `fun t => mul_nonneg (by positivity) (hEpos t)`.

Establish `hVn : ∀ t, 0 ≤ V t` using `fun t => mul_nonneg (by positivity) (hEpos t)`. Set `D : ℝ → ℝ` to `fun t => 2 * (inner ℝ (ft t) (z * ft t + g t)) * E t + ‖ft t‖ ^ 2 * (E t * (-2 * s))`. Establish `hD : Continuous D`. Establish `: Continuous fun t => inner ℝ (ft t) (z * ft t + g t)` using `Continuous.inner hft (by fun_prop)`. Use `fun_prop`.

Establish `hDge : ∀ t, a * U t - (1 / a) * V t ≤ D t` using `fun t => by`. Use `energy_lower z (ft t) (g t) s a (E t) ha (hEpos t)` as an intermediate fact. Rewrite `this` using `[← hadef]`. Establish `e : 2 * a - a = a` using `by ring`. Rewrite `this` using `[e]`.

Conclude with `this`. Establish `hderiv : ∀ t, 0 ≤ t → HasDerivAt (fun x => ‖f x‖ ^ 2 * E x) (D t) t`. Introduce `t ht`. Establish `h1` using `(hf t ht).norm_sq`. Establish `h2 : HasDerivAt E (E t * (-2 * s)) t`.

Use `((hasDerivAt_id t).const_mul (-2 * s)).exp` as an intermediate fact. Simplify `this` using `[E]`. Establish `e : D t = 2 * (inner ℝ (f t) (z * f t + g t)) * E t + ‖f t‖ ^ 2 * (E t * (-2 * s))`. Simplify using `only [D, hfe t ht]`. Rewrite using `[e]`.

Conclude with `h1.mul h2`. Establish `hVlin : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (V t)) < ⊤`. Use `lt_of_le_of_lt (le_of_eq ?_) hgi` and prove the remaining obligations. Use `lintegral_congr fun t => ?_` and prove the remaining obligations. Simplify using `only [V, E]`.

Rewrite using `[ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`. Establish `hVint : IntegrableOn V (Ioi 0)` using `⟨hV.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hVn)).2 hVlin⟩`. Use `set C : ℝ := ∫ t in Ioi (0 : ℝ), V t with hC`. Establish `hVle : ∀ t T, 0 ≤ t → t ≤ T → ∫ r in t..T, V r ≤ C`. Introduce `t T ht hT`.

Rewrite using `[intervalIntegral.integral_of_le hT]`. Conclude with `setIntegral_mono_set hVint (ae_of_all _ hVn) (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ht)).eventuallyLE`. Establish `hWlin : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (‖f t‖ ^ 2 * Real.exp (-2 * s' * t))) < ⊤`. Use `lt_of_le_of_lt (le_of_eq ?_) hfi` and prove the remaining obligations. Use `lintegral_congr fun t => ?_` and prove the remaining obligations.

Rewrite using `[ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`. Set `Fz : ℝ → ℂ` to `fun r => Complex.exp (-z * r) * f r`. Set `Fd : ℝ → ℂ` to `fun r => Complex.exp (-z * r) * g r`. Establish `hFdc : Continuous Fd` using `by fun_prop`. Establish `hFd : ∀ r, 0 ≤ r → HasDerivAt Fz (Fd r) r`.

Introduce `r hr`. Establish `h0 : HasDerivAt (fun r : ℝ => -z * (r : ℂ)) (-z) r`. Simplify using `using (Complex.ofRealCLM.hasDerivAt (x := r)).const_mul (-z)`. Establish `h1` using `h0.cexp.mul (hf r hr)`. Use `h1.congr_deriv ?_` and prove the remaining obligations.

Simplify using `only [Fd]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnexp : ∀ r : ℝ, ‖Complex.exp (-z * r)‖ = Real.exp (-z.re * r)`. Introduce `r`. Rewrite using `[Complex.norm_exp]`.

Simplify using the standard rewrite rules. Set `x : ℝ → ℝ` to `fun r => ‖g r‖ * Real.exp (-s * r)`. Establish `hxc : Continuous x` using `by fun_prop`. Establish `hx2 : ∀ r, x r ^ 2 = V r`. Introduce `r`.

Simplify using `only [x, V, E]`. Rewrite using `[mul_pow, sq (Real.exp _), ← Real.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `hFdn : ∀ r, ‖Fd r‖ = Real.exp (-a * r) * x r`.

Introduce `r`. Simplify using `only [Fd, x]`. Rewrite using `[norm_mul, hnexp]`. Establish `e : Real.exp (-z.re * r) = Real.exp (-a * r) * Real.exp (-s * r)`. Rewrite using `[← Real.exp_add, hadef]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨K, hK⟩ : ∃ K : ℝ, K = C / 2 + 1 / (4 * a)` from `⟨_, rfl⟩`.

Establish `hUb : ∀ t, 0 ≤ t → ‖f t‖ * Real.exp (-s * t) ≤ K`. Introduce `t ht`. Use `le_of_forall_pos_le_add fun ε hε => ?_` and prove the remaining obligations. Establish `hpos : 0 < (ε * Real.exp (-a * t)) ^ 2` using `by positivity`. Take `⟨T, hT, hTW⟩` from `exists_small_of_lintegral _ hWlin t ht _ hpos`.

Establish `hT0 : 0 ≤ T` using `ht.trans hT`. Establish `hFT : ‖Fz T‖ ≤ ε * Real.exp (-a * t)`. Establish `h1 : ‖Fz T‖ ^ 2 ≤ ‖f T‖ ^ 2 * Real.exp (-2 * s' * T)`. Simplify using `only [Fz]`. Rewrite using `[norm_mul, hnexp, mul_pow, sq (Real.exp _), ← Real.exp_add, mul_comm]`.

Use `mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)` and prove the remaining obligations. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 hs') hT0]`. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (h1.trans hTW.le)`. Establish `hdiff : ‖Fz t‖ ≤ ‖Fz T‖ + ∫ r in t..T, ‖Fd r‖`. Establish `hI : ∫ r in t..T, Fd r = Fz T - Fz t`.

Use `intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r hr => ?_) (hFdc.intervalIntegrable _ _)` and prove the remaining obligations. Rewrite `hr` using `[uIcc_of_le hT]`. Conclude with `hFd r (ht.trans hr.1)`. Establish `hn` using `intervalIntegral.norm_integral_le_integral_norm (f := Fd) (μ := volume) hT`. Rewrite `hn` using `[hI]`.

Establish `h2` using `norm_sub_norm_le (Fz t) (Fz T)`. Rewrite `h2` using `[norm_sub_rev]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hint : ∫ r in t..T, ‖Fd r‖ ≤ Real.exp (-a * t) * K`. Establish `h3` using `young_tail a C ha x hxc t T hT (by`.

Simplify using `only [hx2]`. Conclude with `hVle t T ht hT)`. Simplify using `only [hFdn]`. Rewrite using `[hK]`. Conclude with `h3`.

Establish `hFt : ‖Fz t‖ * Real.exp (a * t) = ‖f t‖ * Real.exp (-s * t)`. Simplify using `only [Fz]`. Rewrite using `[norm_mul, hnexp]`. Establish `e : Real.exp (-s * t) = Real.exp (-z.re * t) * Real.exp (a * t)`. Rewrite using `[← Real.exp_add, hadef]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcan : Real.exp (-a * t) * Real.exp (a * t) = 1`.

Rewrite using `[← Real.exp_add]`. Simplify using the standard rewrite rules. Establish `h4 : ‖Fz t‖ ≤ (ε + K) * Real.exp (-a * t)` using `by linarith`. Establish `h5` using `mul_le_mul_of_nonneg_right h4 (Real.exp_pos (a * t)).le`. Rewrite `h5` using `[hFt, mul_assoc, hcan, mul_one]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hCn : 0 ≤ C` using `setIntegral_nonneg measurableSet_Ioi fun t _ => hVn t`. Establish `hbound : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, U t ≤ (K ^ 2 + (1 / a) * C) / a`. Introduce `T hT`. Establish `hI : ∫ t in (0 : ℝ)..T, D t = ‖f T‖ ^ 2 * E T - ‖f 0‖ ^ 2 * E 0`.

Use `intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => ‖f x‖ ^ 2 * E x) (fun t ht => ?_) (hD.intervalIntegrable _ _)` and prove the remaining obligations. Rewrite `ht` using `[uIcc_of_le hT]`. Conclude with `hderiv t ht.1`. Establish `hmono : ∫ t in (0 : ℝ)..T, (a * U t - (1 / a) * V t) ≤ ∫ t in (0 : ℝ)..T, D t` using `intervalIntegral.integral_mono_on hT (((continuous_const.mul hU).sub (continuous_const.mul hV)).intervalIntegrable _ _) (hD.intervalIntegrable _ _) (fun t _ => hDge t)`. Establish `hsplit : ∫ t in (0 : ℝ)..T, (a * U t - (1 / a) * V t) = a * (∫ t in (0 : ℝ)..T, U t) - (1 / a) * ∫ t in (0 : ℝ)..T, V t`.

Establish `c1 : IntervalIntegrable (fun t => a * U t) volume 0 T` using `(continuous_const.mul hU).intervalIntegrable _ _`. Establish `c2 : IntervalIntegrable (fun t => (1 / a) * V t) volume 0 T` using `(continuous_const.mul hV).intervalIntegrable _ _`. Rewrite using `[intervalIntegral.integral_sub c1 c2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]`. Establish `hUT : ‖f T‖ ^ 2 * E T ≤ K ^ 2`. Establish `h1` using `pow_le_pow_left₀ (by positivity) (hUb T hT) 2`.

Establish `e : (‖f T‖ * Real.exp (-s * T)) ^ 2 = ‖f T‖ ^ 2 * E T`. Simplify using `only [E]`. Rewrite using `[mul_pow, sq (Real.exp _), ← Real.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h1` using `[e]`. Then use the resulting hypothesis. Establish `h0 : 0 ≤ ‖f 0‖ ^ 2 * E 0` using `mul_nonneg (by positivity) (hEpos 0)`. Establish `hVa : (1 / a) * ∫ t in (0 : ℝ)..T, V t ≤ (1 / a) * C` using `mul_le_mul_of_nonneg_left (hVle 0 T le_rfl hT) (by positivity)`. Rewrite using `[le_div_iff₀ ha]`. Rewrite `hmono` using `[hI, hsplit]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hUint : IntegrableOn U (Ioi 0)`. Use `integrableOn_Ioi_of_intervalIntegral_norm_bounded ((K ^ 2 + (1 / a) * C) / a) 0 (l := atTop) (b := fun T : ℝ => T) (fun T => (hU.integrableOn_Icc (a := 0) (b := T)).mono_set Ioc_subset_Icc_self) tendsto_id ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT`. Simplify `hbound T hT` using `only [Real.norm_eq_abs, abs_of_nonneg (hUn _)]`.

Establish `hfin` using `hUint.lintegral_lt_top`. Use `lt_of_le_of_lt (le_of_eq ?_) hfin` and prove the remaining obligations. Use `setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_` and prove the remaining obligations. Establish `ht0 : (0 : ℝ) ≤ t` using `le_of_lt ht`. Simplify using `only [U, E, hfe t ht0]`.

Rewrite using `[ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`.
-/
theorem odeB : CompanionTheory.RgExh.Dec.N.OdeB := by
  intro z s s' hs hs' f g hf hg hgi hfi
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = z.re - s := ⟨_, rfl⟩
  have ha : 0 < a := by rw [hadef]; exact sub_pos.2 hs

  let ft : ℝ → ℂ := fun t => f (max t 0)
  have hfon : ContinuousOn f (Ici 0) := fun t ht =>
    (hf t ht).continuousAt.continuousWithinAt
  have hft : Continuous ft :=
    hfon.comp_continuous (continuous_id.max continuous_const) (fun t => mem_Ici.2 (le_max_right _ _))
  have hfe : ∀ t, 0 ≤ t → ft t = f t := fun t ht => by simp [ft, max_eq_left ht]
  let E : ℝ → ℝ := fun t => Real.exp (-2 * s * t)
  have hE : Continuous E := by fun_prop
  have hEpos : ∀ t, 0 ≤ E t := fun t => (Real.exp_pos _).le
  let U : ℝ → ℝ := fun t => ‖ft t‖ ^ 2 * E t
  let V : ℝ → ℝ := fun t => ‖g t‖ ^ 2 * E t
  have hU : Continuous U := by fun_prop
  have hV : Continuous V := by fun_prop
  have hUn : ∀ t, 0 ≤ U t := fun t => mul_nonneg (by positivity) (hEpos t)
  have hVn : ∀ t, 0 ≤ V t := fun t => mul_nonneg (by positivity) (hEpos t)
  let D : ℝ → ℝ := fun t =>
    2 * (inner ℝ (ft t) (z * ft t + g t)) * E t + ‖ft t‖ ^ 2 * (E t * (-2 * s))
  have hD : Continuous D := by
    have : Continuous fun t => inner ℝ (ft t) (z * ft t + g t) :=
      Continuous.inner hft (by fun_prop)
    fun_prop
  have hDge : ∀ t, a * U t - (1 / a) * V t ≤ D t := fun t => by
    have := energy_lower z (ft t) (g t) s a (E t) ha (hEpos t)
    rw [← hadef] at this
    have e : 2 * a - a = a := by ring
    rw [e] at this
    exact this
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt (fun x => ‖f x‖ ^ 2 * E x) (D t) t := by
    intro t ht
    have h1 := (hf t ht).norm_sq
    have h2 : HasDerivAt E (E t * (-2 * s)) t := by
      have := ((hasDerivAt_id t).const_mul (-2 * s)).exp
      simpa [E] using this
    have e : D t = 2 * (inner ℝ (f t) (z * f t + g t)) * E t + ‖f t‖ ^ 2 * (E t * (-2 * s)) := by
      simp only [D, hfe t ht]
    rw [e]
    exact h1.mul h2

  have hVlin : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (V t)) < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) hgi
    refine lintegral_congr fun t => ?_
    simp only [V, E]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm]
  have hVint : IntegrableOn V (Ioi 0) :=
    ⟨hV.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ hVn)).2 hVlin⟩
  set C : ℝ := ∫ t in Ioi (0 : ℝ), V t with hC
  have hVle : ∀ t T, 0 ≤ t → t ≤ T → ∫ r in t..T, V r ≤ C := by
    intro t T ht hT
    rw [intervalIntegral.integral_of_le hT]
    exact setIntegral_mono_set hVint (ae_of_all _ hVn)
      (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ht)).eventuallyLE

  have hWlin : (∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (‖f t‖ ^ 2 * Real.exp (-2 * s' * t))) < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) hfi
    refine lintegral_congr fun t => ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm]

  let Fz : ℝ → ℂ := fun r => Complex.exp (-z * r) * f r
  let Fd : ℝ → ℂ := fun r => Complex.exp (-z * r) * g r
  have hFdc : Continuous Fd := by fun_prop
  have hFd : ∀ r, 0 ≤ r → HasDerivAt Fz (Fd r) r := by
    intro r hr
    have h0 : HasDerivAt (fun r : ℝ => -z * (r : ℂ)) (-z) r := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := r)).const_mul (-z)
    have h1 := h0.cexp.mul (hf r hr)
    refine h1.congr_deriv ?_
    simp only [Fd]
    ring
  have hnexp : ∀ r : ℝ, ‖Complex.exp (-z * r)‖ = Real.exp (-z.re * r) := by
    intro r
    rw [Complex.norm_exp]
    simp
  let x : ℝ → ℝ := fun r => ‖g r‖ * Real.exp (-s * r)
  have hxc : Continuous x := by fun_prop
  have hx2 : ∀ r, x r ^ 2 = V r := by
    intro r
    simp only [x, V, E]
    rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
    congr 2
    ring
  have hFdn : ∀ r, ‖Fd r‖ = Real.exp (-a * r) * x r := by
    intro r
    simp only [Fd, x]
    rw [norm_mul, hnexp]
    have e : Real.exp (-z.re * r) = Real.exp (-a * r) * Real.exp (-s * r) := by
      rw [← Real.exp_add, hadef]
      congr 1
      ring
    rw [e]
    ring
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C / 2 + 1 / (4 * a) := ⟨_, rfl⟩

  have hUb : ∀ t, 0 ≤ t → ‖f t‖ * Real.exp (-s * t) ≤ K := by
    intro t ht
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hpos : 0 < (ε * Real.exp (-a * t)) ^ 2 := by positivity
    obtain ⟨T, hT, hTW⟩ := exists_small_of_lintegral _ hWlin t ht _ hpos
    have hT0 : 0 ≤ T := ht.trans hT
    have hFT : ‖Fz T‖ ≤ ε * Real.exp (-a * t) := by
      have h1 : ‖Fz T‖ ^ 2 ≤ ‖f T‖ ^ 2 * Real.exp (-2 * s' * T) := by
        simp only [Fz]
        rw [norm_mul, hnexp, mul_pow, sq (Real.exp _), ← Real.exp_add, mul_comm]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
        nlinarith [mul_nonneg (sub_nonneg.2 hs') hT0]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1
        (h1.trans hTW.le)
    have hdiff : ‖Fz t‖ ≤ ‖Fz T‖ + ∫ r in t..T, ‖Fd r‖ := by
      have hI : ∫ r in t..T, Fd r = Fz T - Fz t := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r hr => ?_)
          (hFdc.intervalIntegrable _ _)
        rw [uIcc_of_le hT] at hr
        exact hFd r (ht.trans hr.1)
      have hn := intervalIntegral.norm_integral_le_integral_norm (f := Fd) (μ := volume) hT
      rw [hI] at hn
      have h2 := norm_sub_norm_le (Fz t) (Fz T)
      rw [norm_sub_rev] at h2
      linarith
    have hint : ∫ r in t..T, ‖Fd r‖ ≤ Real.exp (-a * t) * K := by
      have h3 := young_tail a C ha x hxc t T hT (by
        simp only [hx2]
        exact hVle t T ht hT)
      simp only [hFdn]
      rw [hK]
      exact h3
    have hFt : ‖Fz t‖ * Real.exp (a * t) = ‖f t‖ * Real.exp (-s * t) := by
      simp only [Fz]
      rw [norm_mul, hnexp]
      have e : Real.exp (-s * t) = Real.exp (-z.re * t) * Real.exp (a * t) := by
        rw [← Real.exp_add, hadef]
        congr 1
        ring
      rw [e]
      ring
    have hcan : Real.exp (-a * t) * Real.exp (a * t) = 1 := by
      rw [← Real.exp_add]
      simp
    have h4 : ‖Fz t‖ ≤ (ε + K) * Real.exp (-a * t) := by linarith
    have h5 := mul_le_mul_of_nonneg_right h4 (Real.exp_pos (a * t)).le
    rw [hFt, mul_assoc, hcan, mul_one] at h5
    linarith

  have hCn : 0 ≤ C := setIntegral_nonneg measurableSet_Ioi fun t _ => hVn t
  have hbound : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, U t ≤ (K ^ 2 + (1 / a) * C) / a := by
    intro T hT
    have hI : ∫ t in (0 : ℝ)..T, D t = ‖f T‖ ^ 2 * E T - ‖f 0‖ ^ 2 * E 0 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun x => ‖f x‖ ^ 2 * E x) (fun t ht => ?_) (hD.intervalIntegrable _ _)
      rw [uIcc_of_le hT] at ht
      exact hderiv t ht.1
    have hmono : ∫ t in (0 : ℝ)..T, (a * U t - (1 / a) * V t) ≤ ∫ t in (0 : ℝ)..T, D t :=
      intervalIntegral.integral_mono_on hT
        (((continuous_const.mul hU).sub (continuous_const.mul hV)).intervalIntegrable _ _)
        (hD.intervalIntegrable _ _) (fun t _ => hDge t)
    have hsplit : ∫ t in (0 : ℝ)..T, (a * U t - (1 / a) * V t) =
        a * (∫ t in (0 : ℝ)..T, U t) - (1 / a) * ∫ t in (0 : ℝ)..T, V t := by
      have c1 : IntervalIntegrable (fun t => a * U t) volume 0 T :=
        (continuous_const.mul hU).intervalIntegrable _ _
      have c2 : IntervalIntegrable (fun t => (1 / a) * V t) volume 0 T :=
        (continuous_const.mul hV).intervalIntegrable _ _
      rw [intervalIntegral.integral_sub c1 c2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hUT : ‖f T‖ ^ 2 * E T ≤ K ^ 2 := by
      have h1 := pow_le_pow_left₀ (by positivity) (hUb T hT) 2
      have e : (‖f T‖ * Real.exp (-s * T)) ^ 2 = ‖f T‖ ^ 2 * E T := by
        simp only [E]
        rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
        congr 2
        ring
      rwa [e] at h1
    have h0 : 0 ≤ ‖f 0‖ ^ 2 * E 0 := mul_nonneg (by positivity) (hEpos 0)
    have hVa : (1 / a) * ∫ t in (0 : ℝ)..T, V t ≤ (1 / a) * C :=
      mul_le_mul_of_nonneg_left (hVle 0 T le_rfl hT) (by positivity)
    rw [le_div_iff₀ ha]
    rw [hI, hsplit] at hmono
    nlinarith
  have hUint : IntegrableOn U (Ioi 0) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
      ((K ^ 2 + (1 / a) * C) / a) 0 (l := atTop) (b := fun T : ℝ => T)
      (fun T => (hU.integrableOn_Icc (a := 0) (b := T)).mono_set Ioc_subset_Icc_self) tendsto_id ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hUn _)] using hbound T hT
  have hfin := hUint.lintegral_lt_top
  refine lt_of_le_of_lt (le_of_eq ?_) hfin
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  simp only [U, E, hfe t ht0]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm_eq_enorm]

end GlobalTheory.CompanionTheory.OdeRoots.Above
