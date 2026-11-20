import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set Filter Topology Real

/- English proof (translation)
Introduce `b`. Proceed by induction on `b with`. Consider the case `zero`. Establish `hderiv : ∀ x ∈ Ici (0:ℝ), HasDerivAt (fun t : ℝ => -(1 / ((k + 1 : ℝ) * (c + t) ^ (k + 1)))) ((fun t : ℝ => t ^ 0 / (c + t) ^ (0 + 2 + k)) x) x`. Introduce `x hx`.

Establish `hx' : 0 < c + x` using `by have := mem_Ici.mp hx; linarith`. Establish `h1 : HasDerivAt (fun t : ℝ => (k + 1 : ℝ) * (c + t) ^ (k + 1)) ((k + 1 : ℝ) * ((k + 1 : ℕ) * (c + x) ^ k * 1)) x`. Conclude with `((((hasDerivAt_id x).const_add c).pow (k + 1))).const_mul _`. Establish `h2` using `(h1.inv (by positivity)).neg`. Establish `hfun : (fun t : ℝ => -(1 / ((k + 1 : ℝ) * (c + t) ^ (k + 1)))) = -(fun t : ℝ => (k + 1 : ℝ) * (c + t) ^ (k + 1))⁻¹`.

Use function extensionality and compare the values at `t`. Simplify using `[one_div]`. Rewrite using `[hfun]`. Use `h2.congr_deriv ?_` and prove the remaining obligations. Establish `hne : (c + x) ≠ 0` using `hx'.ne'`.

Simplify using `only [pow_zero]`. Clear the denominators using the available nonvanishing facts. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : ∀ x ∈ Ioi (0:ℝ), 0 ≤ (fun t : ℝ => t ^ 0 / (c + t) ^ (0 + 2 + k)) x`.

Introduce `x hx`. Establish `: 0 < c + x` using `by have := mem_Ioi.mp hx; linarith`. Check the signs of the components of the expression. Establish `hlim : Tendsto (fun t : ℝ => -(1 / ((k + 1 : ℝ) * (c + t) ^ (k + 1)))) atTop (𝓝 0)`. Establish `h0 : Tendsto (fun t : ℝ => (k + 1 : ℝ) * (c + t) ^ (k + 1)) atTop atTop`.

Use `Tendsto.const_mul_atTop (by positivity) ?_` and prove the remaining obligations. Conclude with `(tendsto_pow_atTop (by omega)).comp (tendsto_atTop_add_const_left _ c tendsto_id)`. Use `(tendsto_inv_atTop_zero.comp h0).neg` as an intermediate fact. Simplify `this` using `[one_div]`. Use `⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim, ?_⟩` and prove the remaining obligations.

Rewrite using `[integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]`. Simplify using `only [Nat.factorial_zero, one_mul, zero_add, add_zero]`. Establish `hk : ((k + 1).factorial : ℝ) = (k + 1) * k.factorial`. Move the coercions through the operations in `[Nat.factorial_succ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hk]`. Establish `: (k.factorial : ℝ) ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Consider the case `succ b ih`.

Take `⟨hint, hval⟩` from `ih`. Establish `hint' : IntegrableOn (fun t : ℝ => t ^ (b + 1) / (c + t) ^ (b + 1 + 2 + k)) (Ioi 0)`. Use `hint.mono' ?_ ?_` and prove the remaining obligations. Use `ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi` and prove the remaining obligations. Introduce `x hx`.

Establish `: 0 < c + x` using `by have := mem_Ioi.mp hx; linarith`. Conclude with `((continuous_pow _).continuousAt.div (by fun_prop) (by positivity)).continuousWithinAt`. Use `(ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)` and prove the remaining obligations. Establish `hx0 : 0 < x` using `hx`. Establish `hcx : 0 < c + x` using `by linarith`.

Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by positivity)]`. Rewrite using `[div_le_div_iff₀ (by positivity) (by positivity)]`. Establish `e1 : (c + x) ^ (b + 1 + 2 + k) = (c + x) ^ (b + 2 + k) * (c + x)` using `by ring`. Rewrite using `[e1, pow_succ]`. Use `mul_le_mul_of_nonneg_left (show x ≤ c + x by linarith) (show 0 ≤ x ^ b * (c + x) ^ (b + 2 + k) by positivity)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Use `⟨hint', ?_⟩` and prove the remaining obligations. Use `set G : ℝ → ℝ := fun t => t ^ (b + 1) / (c + t) ^ (b + 2 + k) with hG`. Use `set G' : ℝ → ℝ := fun t => (b + 1 : ℝ) * (t ^ b / (c + t) ^ (b + 2 + k)) - (b + 2 + k : ℝ) * (t ^ (b + 1) / (c + t) ^ (b + 1 + 2 + k)) with hG'`. Establish `hderiv : ∀ x ∈ Ici (0:ℝ), HasDerivAt G (G' x) x`.

Introduce `x hx`. Establish `hcx : 0 < c + x` using `by have := mem_Ici.mp hx; linarith`. Establish `h0 : HasDerivAt (fun t : ℝ => c + t) 1 x` using `(hasDerivAt_id x).const_add c`. Establish `h1 : HasDerivAt G (((b + 1 : ℕ) * x ^ b * (c + x) ^ (b + 2 + k) - x ^ (b + 1) * ((b + 2 + k : ℕ) * (c + x) ^ (b + 2 + k - 1) * 1)) / ((c + x) ^ (b + 2 + k)) ^ 2) x` using `(hasDerivAt_pow (b + 1) x).div (h0.pow (b + 2 + k)) (pow_pos hcx _).ne'`. Use `h1.congr_deriv ?_` and prove the remaining obligations.

Simplify using `only [hG']`. Establish `hne : (c + x) ≠ 0` using `hcx.ne'`. Rewrite using `[show b + 2 + k - 1 = b + 1 + k by omega]`. Clear the denominators using the available nonvanishing facts. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hG'int : IntegrableOn G' (Ioi 0)` using `(hint.const_mul _).sub (hint'.const_mul _)`. Establish `hlim : Tendsto G atTop (𝓝 0)`. Establish `hup : Tendsto (fun t : ℝ => 1 / (c + t) ^ (k + 1)) atTop (𝓝 0)`. Establish `h0 : Tendsto (fun t : ℝ => (c + t) ^ (k + 1)) atTop atTop` using `(tendsto_pow_atTop (by omega)).comp (tendsto_atTop_add_const_left _ c tendsto_id)`.

Simplify `tendsto_inv_atTop_zero.comp h0` using `[one_div, Function.comp_def]`. Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop 0] with t ht`. Establish `: 0 < c + t` using `by linarith`. Check the signs of the components of the expression.

Use `filter_upwards [eventually_ge_atTop 0] with t ht`. Establish `hct : 0 < c + t` using `by linarith`. Simplify using `only [hG]`. Rewrite using `[div_le_div_iff₀ (by positivity) (by positivity), one_mul]`. Establish `h1 : t ^ (b + 1) ≤ (c + t) ^ (b + 1)` using `pow_le_pow_left₀ ht (by linarith) _`.

Establish `h2 : (c + t) ^ (b + 1) * (c + t) ^ (k + 1) = (c + t) ^ (b + 2 + k)`. Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← h2]`.

Conclude with `mul_le_mul_of_nonneg_right h1 (by positivity)`. Establish `key` using `integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hG'int hlim`. Simplify using `only [hG, hG'] at key`. Rewrite `key` using `[integral_sub (hint.const_mul _) (hint'.const_mul _), integral_const_mul, integral_const_mul, hval]`. Simplify using `only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow, zero_div, sub_zero] at key`.

Establish `hb2 : (b + 2 + k : ℝ) ≠ 0` using `by positivity`. Establish `e : ∫ t in Ioi (0:ℝ), t ^ (b + 1) / (c + t) ^ (b + 1 + 2 + k) = (b + 1 : ℝ) * (((b.factorial * k.factorial : ℕ) : ℝ) / (b + k + 1).factorial / c ^ (k + 1)) / (b + 2 + k)`. Rewrite using `[eq_div_iff hb2]`. Take the linear combination `-key`. Rewrite using `[e]`.

Establish `hf : ((b + 1 + k + 1).factorial : ℝ) = (b + k + 2) * (b + k + 1).factorial`. Rewrite using `[show b + 1 + k + 1 = (b + k + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring`. Rewrite using `[hf, show (b + 1).factorial = (b + 1) * b.factorial from Nat.factorial_succ b]`. Use `push_cast`. Establish `: ((b + k + 1).factorial : ℝ) ≠ 0` using `by positivity`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_Ioi_pow_div_add_pow (c : ℝ) (hc : 0 < c) (k : ℕ) : ∀ b : ℕ,
    IntegrableOn (fun t : ℝ => t ^ b / (c + t) ^ (b + 2 + k)) (Ioi 0) ∧
    ∫ t in Ioi (0:ℝ), t ^ b / (c + t) ^ (b + 2 + k) =
      ((b.factorial * k.factorial : ℕ) : ℝ) / (b + k + 1).factorial / c ^ (k + 1) := by
  intro b
  induction b with
  | zero =>
    have hderiv : ∀ x ∈ Ici (0:ℝ), HasDerivAt (fun t : ℝ => -(1 / ((k + 1 : ℝ) * (c + t) ^ (k + 1))))
        ((fun t : ℝ => t ^ 0 / (c + t) ^ (0 + 2 + k)) x) x := by
      intro x hx
      have hx' : 0 < c + x := by have := mem_Ici.mp hx; linarith
      have h1 : HasDerivAt (fun t : ℝ => (k + 1 : ℝ) * (c + t) ^ (k + 1))
          ((k + 1 : ℝ) * ((k + 1 : ℕ) * (c + x) ^ k * 1)) x := by
        exact ((((hasDerivAt_id x).const_add c).pow (k + 1))).const_mul _
      have h2 := (h1.inv (by positivity)).neg
      have hfun : (fun t : ℝ => -(1 / ((k + 1 : ℝ) * (c + t) ^ (k + 1)))) =
          -(fun t : ℝ => (k + 1 : ℝ) * (c + t) ^ (k + 1))⁻¹ := by
        funext t; simp [one_div]
      rw [hfun]
      refine h2.congr_deriv ?_
      have hne : (c + x) ≠ 0 := hx'.ne'
      simp only [pow_zero]
      field_simp
      push_cast
      ring
    have hpos : ∀ x ∈ Ioi (0:ℝ), 0 ≤ (fun t : ℝ => t ^ 0 / (c + t) ^ (0 + 2 + k)) x := by
      intro x hx
      have : 0 < c + x := by have := mem_Ioi.mp hx; linarith
      positivity
    have hlim : Tendsto (fun t : ℝ => -(1 / ((k + 1 : ℝ) * (c + t) ^ (k + 1)))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun t : ℝ => (k + 1 : ℝ) * (c + t) ^ (k + 1)) atTop atTop := by
        refine Tendsto.const_mul_atTop (by positivity) ?_
        exact (tendsto_pow_atTop (by omega)).comp (tendsto_atTop_add_const_left _ c tendsto_id)
      have := (tendsto_inv_atTop_zero.comp h0).neg
      simpa [one_div] using this
    refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim, ?_⟩
    rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
    simp only [Nat.factorial_zero, one_mul, zero_add, add_zero]
    have hk : ((k + 1).factorial : ℝ) = (k + 1) * k.factorial := by
      push_cast [Nat.factorial_succ]; ring
    rw [hk]
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  | succ b ih =>
    obtain ⟨hint, hval⟩ := ih
    have hint' : IntegrableOn (fun t : ℝ => t ^ (b + 1) / (c + t) ^ (b + 1 + 2 + k)) (Ioi 0) := by
      refine hint.mono' ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
        intro x hx
        have : 0 < c + x := by have := mem_Ioi.mp hx; linarith
        exact ((continuous_pow _).continuousAt.div (by fun_prop) (by positivity)).continuousWithinAt
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
        have hx0 : 0 < x := hx
        have hcx : 0 < c + x := by linarith
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have e1 : (c + x) ^ (b + 1 + 2 + k) = (c + x) ^ (b + 2 + k) * (c + x) := by ring
        rw [e1, pow_succ]
        have := mul_le_mul_of_nonneg_left (show x ≤ c + x by linarith)
            (show 0 ≤ x ^ b * (c + x) ^ (b + 2 + k) by positivity)
        nlinarith
    refine ⟨hint', ?_⟩
    set G : ℝ → ℝ := fun t => t ^ (b + 1) / (c + t) ^ (b + 2 + k) with hG
    set G' : ℝ → ℝ := fun t => (b + 1 : ℝ) * (t ^ b / (c + t) ^ (b + 2 + k)) -
      (b + 2 + k : ℝ) * (t ^ (b + 1) / (c + t) ^ (b + 1 + 2 + k)) with hG'
    have hderiv : ∀ x ∈ Ici (0:ℝ), HasDerivAt G (G' x) x := by
      intro x hx
      have hcx : 0 < c + x := by have := mem_Ici.mp hx; linarith
      have h0 : HasDerivAt (fun t : ℝ => c + t) 1 x := (hasDerivAt_id x).const_add c
      have h1 : HasDerivAt G (((b + 1 : ℕ) * x ^ b * (c + x) ^ (b + 2 + k) -
          x ^ (b + 1) * ((b + 2 + k : ℕ) * (c + x) ^ (b + 2 + k - 1) * 1)) /
          ((c + x) ^ (b + 2 + k)) ^ 2) x :=
        (hasDerivAt_pow (b + 1) x).div (h0.pow (b + 2 + k)) (pow_pos hcx _).ne'
      refine h1.congr_deriv ?_
      simp only [hG']
      have hne : (c + x) ≠ 0 := hcx.ne'
      rw [show b + 2 + k - 1 = b + 1 + k by omega]
      field_simp
      push_cast
      ring
    have hG'int : IntegrableOn G' (Ioi 0) :=
      (hint.const_mul _).sub (hint'.const_mul _)
    have hlim : Tendsto G atTop (𝓝 0) := by
      have hup : Tendsto (fun t : ℝ => 1 / (c + t) ^ (k + 1)) atTop (𝓝 0) := by
        have h0 : Tendsto (fun t : ℝ => (c + t) ^ (k + 1)) atTop atTop :=
          (tendsto_pow_atTop (by omega)).comp (tendsto_atTop_add_const_left _ c tendsto_id)
        simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp h0
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
      · filter_upwards [eventually_ge_atTop 0] with t ht
        have : 0 < c + t := by linarith
        positivity
      · filter_upwards [eventually_ge_atTop 0] with t ht
        have hct : 0 < c + t := by linarith
        simp only [hG]
        rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
        have h1 : t ^ (b + 1) ≤ (c + t) ^ (b + 1) := pow_le_pow_left₀ ht (by linarith) _
        have h2 : (c + t) ^ (b + 1) * (c + t) ^ (k + 1) = (c + t) ^ (b + 2 + k) := by
          rw [← pow_add]; congr 1; omega
        rw [← h2]
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have key := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hG'int hlim
    simp only [hG, hG'] at key
    rw [integral_sub (hint.const_mul _) (hint'.const_mul _), integral_const_mul,
      integral_const_mul, hval] at key
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
      zero_div, sub_zero] at key
    have hb2 : (b + 2 + k : ℝ) ≠ 0 := by positivity
    have e : ∫ t in Ioi (0:ℝ), t ^ (b + 1) / (c + t) ^ (b + 1 + 2 + k) =
        (b + 1 : ℝ) * (((b.factorial * k.factorial : ℕ) : ℝ) / (b + k + 1).factorial / c ^ (k + 1))
          / (b + 2 + k) := by
      rw [eq_div_iff hb2]; linear_combination -key
    rw [e]
    have hf : ((b + 1 + k + 1).factorial : ℝ) = (b + k + 2) * (b + k + 1).factorial := by
      rw [show b + 1 + k + 1 = (b + k + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
    rw [hf, show (b + 1).factorial = (b + 1) * b.factorial from Nat.factorial_succ b]
    push_cast
    have : ((b + k + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/- English proof (translation)
Take `⟨hI, hV⟩` from `integral_Ioi_pow_div_add_pow c hc k b`. Use `set f : ℝ → ℝ := fun r => r ^ (2 * b) / (c + r ^ 2) ^ (b + 2 + k) with hf`. Use `set g : ℝ → ℝ := fun t => t ^ b / (c + t) ^ (b + 2 + k) with hg`. Establish `hdim : Module.finrank ℝ ℂ = 2` using `Complex.finrank_real_complex`. Establish `hcongr : EqOn (fun x : ℝ => (|(2:ℝ)| * x ^ ((2:ℝ) - 1)) • g (x ^ (2:ℝ))) (fun y : ℝ => (2:ℝ) * (y ^ (Module.finrank ℝ ℂ - 1) • f y)) (Ioi 0)`.

Introduce `x _`. Simplify using `only [hf, hg, hdim, smul_eq_mul]`. Rewrite using `[show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, abs_two, pow_mul]`. Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : IntegrableOn (fun x : ℝ => (|(2:ℝ)| * x ^ ((2:ℝ) - 1)) • g (x ^ (2:ℝ))) (Ioi 0)` using `(integrableOn_Ioi_comp_rpow_iff g two_ne_zero).mpr hI`. Establish `h3` using `(integrableOn_congr_fun hcongr measurableSet_Ioi).mp h2`. Establish `h4 : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • f y) (Ioi 0)`. Establish `h5 : IntegrableOn (fun y : ℝ => (1/2 : ℝ) * (2 * (y ^ (Module.finrank ℝ ℂ - 1) • f y))) (Ioi 0)` using `h3.const_mul (1/2 : ℝ)`. Use `h5.congr_fun (fun y _ => ?_) measurableSet_Ioi` and prove the remaining obligations.

Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hint : Integrable (fun w : ℂ => f ‖w‖)` using `(integrable_fun_norm_addHaar (volume : Measure ℂ) (f := f)).mpr h4`. Use `⟨hint, ?_⟩` and prove the remaining obligations. Use `show ∫ w : ℂ, f ‖w‖ = _`.

Establish `hball : (volume : Measure ℂ).real (Metric.ball 0 1) = π`. Simplify using `[Measure.real, Complex.volume_ball]`. Establish `hsub` using `integral_comp_rpow_Ioi g (two_ne_zero : (2:ℝ) ≠ 0)`. Rewrite `hsub` using `[setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul]`. Rewrite using `[integral_fun_norm_addHaar (volume : Measure ℂ) f, hball, hdim]`.

Establish `: ∫ y in Ioi (0:ℝ), y ^ (2 - 1) • f y = (∫ t in Ioi (0:ℝ), g t) / 2`. Rewrite using `[← hsub, hdim]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hV]`. Simplify using `only [nsmul_eq_mul, smul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_complex_norm_pow_div (c : ℝ) (hc : 0 < c) (k b : ℕ) :
    Integrable (fun w : ℂ => ‖w‖ ^ (2 * b) / (c + ‖w‖ ^ 2) ^ (b + 2 + k)) ∧
    ∫ w : ℂ, ‖w‖ ^ (2 * b) / (c + ‖w‖ ^ 2) ^ (b + 2 + k) =
      π * (((b.factorial * k.factorial : ℕ) : ℝ) / (b + k + 1).factorial / c ^ (k + 1)) := by
  obtain ⟨hI, hV⟩ := integral_Ioi_pow_div_add_pow c hc k b
  set f : ℝ → ℝ := fun r => r ^ (2 * b) / (c + r ^ 2) ^ (b + 2 + k) with hf
  set g : ℝ → ℝ := fun t => t ^ b / (c + t) ^ (b + 2 + k) with hg
  have hdim : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have hcongr : EqOn (fun x : ℝ => (|(2:ℝ)| * x ^ ((2:ℝ) - 1)) • g (x ^ (2:ℝ)))
      (fun y : ℝ => (2:ℝ) * (y ^ (Module.finrank ℝ ℂ - 1) • f y)) (Ioi 0) := by
    intro x _
    simp only [hf, hg, hdim, smul_eq_mul]
    rw [show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, abs_two, pow_mul]
    norm_num
    ring
  have h2 : IntegrableOn (fun x : ℝ => (|(2:ℝ)| * x ^ ((2:ℝ) - 1)) • g (x ^ (2:ℝ))) (Ioi 0) :=
    (integrableOn_Ioi_comp_rpow_iff g two_ne_zero).mpr hI
  have h3 := (integrableOn_congr_fun hcongr measurableSet_Ioi).mp h2
  have h4 : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • f y) (Ioi 0) := by
    have h5 : IntegrableOn (fun y : ℝ => (1/2 : ℝ) * (2 * (y ^ (Module.finrank ℝ ℂ - 1) • f y)))
        (Ioi 0) := h3.const_mul (1/2 : ℝ)
    refine h5.congr_fun (fun y _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]; ring
  have hint : Integrable (fun w : ℂ => f ‖w‖) :=
    (integrable_fun_norm_addHaar (volume : Measure ℂ) (f := f)).mpr h4
  refine ⟨hint, ?_⟩
  show ∫ w : ℂ, f ‖w‖ = _
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = π := by
    simp [Measure.real, Complex.volume_ball]
  have hsub := integral_comp_rpow_Ioi g (two_ne_zero : (2:ℝ) ≠ 0)
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul] at hsub
  rw [integral_fun_norm_addHaar (volume : Measure ℂ) f, hball, hdim]
  have : ∫ y in Ioi (0:ℝ), y ^ (2 - 1) • f y = (∫ t in Ioi (0:ℝ), g t) / 2 := by
    rw [← hsub, hdim]; ring
  rw [this, hV]
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  ring

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `b c hc`. Simplify using `only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, add_zero, zero_add, pow_zero, one_mul]`.

Rewrite using `[lintegral_const, volume_pi, Measure.pi_univ]`. Simplify using `only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]`. Use `congr 1`. Establish `: (k.factorial : ℝ) ≠ 0` using `by positivity`. Rewrite using `[add_comm 1 k]`.

Clear the denominators using the available nonvanishing facts. Consider the case `succ N ih`. Introduce `b c hc`. Use `set K := ∑ j : Fin N, b j.succ + N + k with hK`. Set `g : ℂ × (Fin N → ℂ) → ENNReal` to `fun p => ENNReal.ofReal ((‖p.1‖ ^ (2 * b 0) * ∏ j : Fin N, ‖p.2 j‖ ^ (2 * b j.succ)) / (c + (‖p.1‖ ^ 2 + ∑ j : Fin N, ‖p.2 j‖ ^ 2)) ^ (b 0 + 2 + K))`.

Establish `hgm : Measurable g` using `by fun_prop`. Establish `e` using `volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℂ) 0`. Establish `hexp : ∑ j, b j + (N + 1) + 1 + k = b 0 + 2 + K`. Rewrite using `[Fin.sum_univ_succ, hK]`. Use linear arithmetic over natural numbers and integers.

Establish `hcomp : ∀ z : Fin (N + 1) → ℂ, ENNReal.ofReal ((∏ j, ‖z j‖ ^ (2 * b j)) / (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + (N + 1) + 1 + k)) = g (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℂ) 0 z)`. Introduce `z`. Rewrite using `[hexp]`. Simplify using `[g, MeasurableEquiv.piFinSuccAbove_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.tail]`. Rewrite using `[lintegral_congr hcomp, e.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), Measure.volume_eq_prod, lintegral_prod_symm _ hgm.aemeasurable]`.

Establish `hinner : ∀ y : Fin N → ℂ, ∫⁻ w : ℂ, g (w, y) = ENNReal.ofReal ((π * (((b 0).factorial * K.factorial : ℕ) : ℝ) / (b 0 + K + 1).factorial) * ((∏ j : Fin N, ‖y j‖ ^ (2 * b j.succ)) / (c + ∑ j, ‖y j‖ ^ 2) ^ (∑ j : Fin N, b j.succ + N + 1 + k)))`. Introduce `y`. Use `set A := ∏ j : Fin N, ‖y j‖ ^ (2 * b j.succ) with hA'`. Use `set c' := c + ∑ j, ‖y j‖ ^ 2 with hc'd`. Establish `hc' : 0 < c'` using `by positivity`.

Establish `hA : 0 ≤ A` using `by positivity`. Take `⟨hI, hV⟩` from `integral_complex_norm_pow_div c' hc' K (b 0)`. Establish `hsplit : ∀ w : ℂ, g (w, y) = ENNReal.ofReal A * ENNReal.ofReal (‖w‖ ^ (2 * b 0) / (c' + ‖w‖ ^ 2) ^ (b 0 + 2 + K))`. Introduce `w`. Simplify using `only [g]`.

Rewrite using `[← ENNReal.ofReal_mul hA]`. Use `congr 1`. Rewrite using `[hc'd, hA', show c + (‖w‖ ^ 2 + ∑ j, ‖y j‖ ^ 2) = c + ∑ j, ‖y j‖ ^ 2 + ‖w‖ ^ 2 by ring]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[lintegral_congr hsplit, lintegral_const_mul _ (by fun_prop), ← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun w => by positivity), hV, ← ENNReal.ofReal_mul hA]`.

Use `congr 1`. Rewrite using `[show ∑ j : Fin N, b j.succ + N + 1 + k = K + 1 by omega]`. Establish `: (c' ^ (K + 1)) ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts. Rewrite using `[lintegral_congr hinner]`.

Establish `hC : 0 ≤ π * (((b 0).factorial * K.factorial : ℕ) : ℝ) / (b 0 + K + 1).factorial`. Check the signs of the components of the expression. Rewrite using `[lintegral_congr (fun y => ENNReal.ofReal_mul hC), lintegral_const_mul _ (by fun_prop), ih (fun j => b j.succ) c hc, ← ENNReal.ofReal_mul hC]`. Use `congr 1`. Rewrite using `[Fin.prod_univ_succ, show ∑ j, b j + (N + 1) + k = b 0 + K + 1 by`.

Rewrite using `[Fin.sum_univ_succ, hK]`. Use the proof step `omega]`. Establish `h1 : (K.factorial : ℝ) ≠ 0` using `by positivity`. Establish `h2 : ((b 0 + K + 1).factorial : ℝ) ≠ 0` using `by positivity`. Establish `h3 : c ^ (k + 1) ≠ 0` using `by positivity`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lintegral_pi_complex_monomial (k : ℕ) : ∀ (N : ℕ) (b : Fin N → ℕ) (c : ℝ), 0 < c →
    ∫⁻ z : Fin N → ℂ, ENNReal.ofReal ((∏ j, ‖z j‖ ^ (2 * b j)) /
        (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k)) =
      ENNReal.ofReal (π ^ N * (∏ j, ((b j).factorial : ℝ)) * k.factorial /
        (∑ j, b j + N + k).factorial / c ^ (k + 1)) := by
  intro N
  induction N with
  | zero =>
    intro b c hc
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, add_zero, zero_add,
      pow_zero, one_mul]
    rw [lintegral_const, volume_pi, Measure.pi_univ]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    congr 1
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    rw [add_comm 1 k]
    field_simp
  | succ N ih =>
    intro b c hc
    set K := ∑ j : Fin N, b j.succ + N + k with hK
    let g : ℂ × (Fin N → ℂ) → ENNReal := fun p => ENNReal.ofReal ((‖p.1‖ ^ (2 * b 0) *
        ∏ j : Fin N, ‖p.2 j‖ ^ (2 * b j.succ)) /
        (c + (‖p.1‖ ^ 2 + ∑ j : Fin N, ‖p.2 j‖ ^ 2)) ^ (b 0 + 2 + K))
    have hgm : Measurable g := by fun_prop
    have e := volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℂ) 0
    have hexp : ∑ j, b j + (N + 1) + 1 + k = b 0 + 2 + K := by
      rw [Fin.sum_univ_succ, hK]; omega
    have hcomp : ∀ z : Fin (N + 1) → ℂ, ENNReal.ofReal ((∏ j, ‖z j‖ ^ (2 * b j)) /
        (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + (N + 1) + 1 + k)) =
        g (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℂ) 0 z) := by
      intro z
      rw [hexp]
      simp [g, MeasurableEquiv.piFinSuccAbove_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.tail]
    rw [lintegral_congr hcomp, e.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
      Measure.volume_eq_prod, lintegral_prod_symm _ hgm.aemeasurable]
    have hinner : ∀ y : Fin N → ℂ, ∫⁻ w : ℂ, g (w, y) = ENNReal.ofReal
        ((π * (((b 0).factorial * K.factorial : ℕ) : ℝ) / (b 0 + K + 1).factorial) *
          ((∏ j : Fin N, ‖y j‖ ^ (2 * b j.succ)) /
            (c + ∑ j, ‖y j‖ ^ 2) ^ (∑ j : Fin N, b j.succ + N + 1 + k))) := by
      intro y
      set A := ∏ j : Fin N, ‖y j‖ ^ (2 * b j.succ) with hA'
      set c' := c + ∑ j, ‖y j‖ ^ 2 with hc'd
      have hc' : 0 < c' := by positivity
      have hA : 0 ≤ A := by positivity
      obtain ⟨hI, hV⟩ := integral_complex_norm_pow_div c' hc' K (b 0)
      have hsplit : ∀ w : ℂ, g (w, y) = ENNReal.ofReal A *
          ENNReal.ofReal (‖w‖ ^ (2 * b 0) / (c' + ‖w‖ ^ 2) ^ (b 0 + 2 + K)) := by
        intro w
        simp only [g]
        rw [← ENNReal.ofReal_mul hA]
        congr 1
        rw [hc'd, hA', show c + (‖w‖ ^ 2 + ∑ j, ‖y j‖ ^ 2) = c + ∑ j, ‖y j‖ ^ 2 + ‖w‖ ^ 2 by ring]
        ring
      rw [lintegral_congr hsplit, lintegral_const_mul _ (by fun_prop),
        ← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun w => by positivity),
        hV, ← ENNReal.ofReal_mul hA]
      congr 1
      rw [show ∑ j : Fin N, b j.succ + N + 1 + k = K + 1 by omega]
      have : (c' ^ (K + 1)) ≠ 0 := by positivity
      field_simp
    rw [lintegral_congr hinner]
    have hC : 0 ≤ π * (((b 0).factorial * K.factorial : ℕ) : ℝ) / (b 0 + K + 1).factorial := by
      positivity
    rw [lintegral_congr (fun y => ENNReal.ofReal_mul hC), lintegral_const_mul _ (by fun_prop),
      ih (fun j => b j.succ) c hc, ← ENNReal.ofReal_mul hC]
    congr 1
    rw [Fin.prod_univ_succ, show ∑ j, b j + (N + 1) + k = b 0 + K + 1 by
      rw [Fin.sum_univ_succ, hK]; omega]
    have h1 : (K.factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((b 0 + K + 1).factorial : ℝ) ≠ 0 := by positivity
    have h3 : c ^ (k + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/- English proof (translation)
Establish `hnn : ∀ z : Fin N → ℂ, 0 ≤ (∏ j, ‖z j‖ ^ (2 * b j)) / (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k)` using `fun z => by positivity`. Establish `hm : AEStronglyMeasurable (fun z : Fin N → ℂ => (∏ j, ‖z j‖ ^ (2 * b j)) / (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k))`. Conclude with `(by fun_prop : Measurable _).aestronglyMeasurable`. Use `⟨⟨hm, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn), lintegral_pi_complex_monomial k N b c hc]`.

Conclude with `ENNReal.ofReal_lt_top`. Rewrite using `[integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hm, lintegral_pi_complex_monomial k N b c hc, ENNReal.toReal_ofReal (by positivity)]`.
-/
theorem integral_pi_complex_monomial (k N : ℕ) (b : Fin N → ℕ) (c : ℝ) (hc : 0 < c) :
    Integrable (fun z : Fin N → ℂ => (∏ j, ‖z j‖ ^ (2 * b j)) /
        (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k)) ∧
    ∫ z : Fin N → ℂ, (∏ j, ‖z j‖ ^ (2 * b j)) / (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k) =
      π ^ N * (∏ j, ((b j).factorial : ℝ)) * k.factorial / (∑ j, b j + N + k).factorial /
        c ^ (k + 1) := by
  have hnn : ∀ z : Fin N → ℂ, 0 ≤ (∏ j, ‖z j‖ ^ (2 * b j)) /
      (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k) := fun z => by positivity
  have hm : AEStronglyMeasurable (fun z : Fin N → ℂ => (∏ j, ‖z j‖ ^ (2 * b j)) /
      (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k)) := by
    exact (by fun_prop : Measurable _).aestronglyMeasurable
  refine ⟨⟨hm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn), lintegral_pi_complex_monomial k N b c hc]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hm,
      lintegral_pi_complex_monomial k N b c hc, ENNReal.toReal_ofReal (by positivity)]

end GroundTheory.Heights₂.Heights
