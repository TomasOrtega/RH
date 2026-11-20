import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivLFunctionStrip
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthGamma
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.CompanionTheory.DigammaStrip

/- English proof (translation)
Establish `hc : ContinuousOn Real.Gamma (Set.Icc (1 / 2) (5 / 2))` using `fun x hx => (Real.differentiableAt_Gamma (fun m h => by`. Establish `h1` using `hx.1`. Establish `h2 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`. Use the proof step `linarith)).continuousAt.continuousWithinAt`. Take `⟨K, hK⟩` from `isCompact_Icc.bddAbove_image hc`.

Conclude with `⟨max K 1, lt_max_of_lt_right one_pos, fun x h1 h2 => (hK ⟨x, ⟨h1, h2⟩, rfl⟩).trans (le_max_left _ _)⟩`.
-/
theorem exists_Gamma_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 5 / 2 → Real.Gamma x ≤ K := by
  have hc : ContinuousOn Real.Gamma (Set.Icc (1 / 2) (5 / 2)) := fun x hx =>
    (Real.differentiableAt_Gamma (fun m h => by
      have h1 := hx.1
      have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)).continuousAt.continuousWithinAt
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hc
  exact ⟨max K 1, lt_max_of_lt_right one_pos,
    fun x h1 h2 => (hK ⟨x, ⟨h1, h2⟩, rfl⟩).trans (le_max_left _ _)⟩

/- English proof (translation)
Establish `h1 : ‖Complex.exp (-u * I)‖ ≤ Real.exp |u.im|`. Rewrite using `[Complex.norm_exp]`. Conclude with `Real.exp_le_exp.2 (by simpa using le_abs_self u.im)`. Establish `h2 : ‖Complex.exp (u * I)‖ ≤ Real.exp |u.im|`. Rewrite using `[Complex.norm_exp]`.

Conclude with `Real.exp_le_exp.2 (by simpa using neg_le_abs u.im)`. Rewrite using `[Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]`. Establish `h3` using `norm_sub_le (Complex.exp (-u * I)) (Complex.exp (u * I))`. Simplify using `only [Complex.norm_ofNat]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_sin_le_exp (u : ℂ) : ‖Complex.sin u‖ ≤ Real.exp |u.im| := by
  have h1 : ‖Complex.exp (-u * I)‖ ≤ Real.exp |u.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (by simpa using le_abs_self u.im)
  have h2 : ‖Complex.exp (u * I)‖ ≤ Real.exp |u.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (by simpa using neg_le_abs u.im)
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have h3 := norm_sub_le (Complex.exp (-u * I)) (Complex.exp (u * I))
  simp only [Complex.norm_ofNat]
  linarith

/- English proof (translation)
Establish `hw0 : w.im ≠ 0`. Introduce `h`. Rewrite `h3` using `[h, abs_zero]`. Evaluate the numerical expressions using `at h3`. Establish `hG : Complex.Gamma w ≠ 0` using `Complex.Gamma_ne_zero_of_re_pos (by linarith)`.

Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `hsin : Complex.sin (Real.pi * w) ≠ 0`. Rewrite using `[Complex.sin_ne_zero_iff]`. Introduce `k hk`. Use `congrArg Complex.im hk` as an intermediate fact.

Conclude with `hw0 (by simpa using this)`. Establish `hrefl` using `Complex.Gamma_mul_Gamma_one_sub w`. Establish `hinv : (Complex.Gamma w)⁻¹ = Complex.Gamma (1 - w) * Complex.sin (Real.pi * w) / Real.pi`. Establish `h6 : Complex.Gamma w * Complex.Gamma (1 - w) * Complex.sin (Real.pi * w) = Real.pi`. Rewrite using `[hrefl, div_mul_cancel₀ _ hsin]`.

Use `eq_div_of_mul_eq hpi ?_` and prove the remaining obligations. Rewrite using `[inv_mul_eq_iff_eq_mul₀ hG]`. Take the linear combination `-h6`. Establish `hn1 : (1 - w) ≠ 0` using `fun h => hw0 (by`. Use `congrArg Complex.im h` as an intermediate fact.

Simplify using `using this)`. Establish `hn2 : (2 - w) ≠ 0` using `fun h => hw0 (by`. Use `congrArg Complex.im h` as an intermediate fact. Simplify using `using this)`. Establish `hrec : Complex.Gamma (3 - w) = (2 - w) * ((1 - w) * Complex.Gamma (1 - w))`.

Establish `e1` using `Complex.Gamma_add_one (1 - w) hn1`. Establish `e2` using `Complex.Gamma_add_one (2 - w) hn2`. Rewrite `e2` using `[show (2 - w) + 1 = 3 - w by ring]`. Rewrite `e1` using `[show (1 - w) + 1 = 2 - w by ring]`. Rewrite using `[e2, e1]`.

Establish `hb1 : 1 / 4 ≤ ‖1 - w‖`. Use `h3.trans ?_` and prove the remaining obligations. Use `Complex.abs_im_le_norm (1 - w)` as an intermediate fact. Simplify using `using this`. Establish `hb2 : 1 / 4 ≤ ‖2 - w‖`.

Use `h3.trans ?_` and prove the remaining obligations. Use `Complex.abs_im_le_norm (2 - w)` as an intermediate fact. Simplify using `using this`. Establish `hre3 : (3 - w).re = 3 - w.re` using `by simp`. Establish `hG3 : ‖Complex.Gamma (3 - w)‖ ≤ K` using `(PI.EF.norm_Gamma_le (by rw [hre3]; linarith)).trans (hK _ (by rw [hre3]; linarith) (by rw [hre3]; linarith))`.

Establish `hG1 : ‖Complex.Gamma (1 - w)‖ ≤ 16 * K`. Rewrite `hG3` using `[hrec, norm_mul, norm_mul]`. Establish `hp` using `norm_nonneg (Complex.Gamma (1 - w))`. Establish `: (1 / 4) * ((1 / 4) * ‖Complex.Gamma (1 - w)‖) ≤ ‖2 - w‖ * (‖1 - w‖ * ‖Complex.Gamma (1 - w)‖)` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hs : ‖Complex.sin (Real.pi * w)‖ ≤ Real.exp (Real.pi * |w.im|)`. Use `(norm_sin_le_exp _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`. Simplify using `[abs_mul, abs_of_pos Real.pi_pos]`. Establish `hpi1 : (1 : ℝ) ≤ Real.pi` using `by linarith [Real.pi_gt_three]`.

Rewrite using `[hinv, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]`. Rewrite using `[div_le_iff₀ Real.pi_pos]`. Establish `he` using `Real.exp_pos (Real.pi * |w.im|)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_inv_Gamma_le {K : ℝ} (hK0 : 0 < K)
    (hK : ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 5 / 2 → Real.Gamma x ≤ K) {w : ℂ}
    (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 5 / 2) (h3 : 1 / 4 ≤ |w.im|) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ 16 * K * Real.exp (Real.pi * |w.im|) := by
  have hw0 : w.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at h3
    norm_num at h3
  have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsin : Complex.sin (Real.pi * w) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    have := congrArg Complex.im hk
    exact hw0 (by simpa using this)
  have hrefl := Complex.Gamma_mul_Gamma_one_sub w
  have hinv : (Complex.Gamma w)⁻¹ = Complex.Gamma (1 - w) * Complex.sin (Real.pi * w) / Real.pi := by
    have h6 : Complex.Gamma w * Complex.Gamma (1 - w) * Complex.sin (Real.pi * w) = Real.pi := by
      rw [hrefl, div_mul_cancel₀ _ hsin]
    refine eq_div_of_mul_eq hpi ?_
    rw [inv_mul_eq_iff_eq_mul₀ hG]
    linear_combination -h6
  have hn1 : (1 - w) ≠ 0 := fun h => hw0 (by
    have := congrArg Complex.im h
    simpa using this)
  have hn2 : (2 - w) ≠ 0 := fun h => hw0 (by
    have := congrArg Complex.im h
    simpa using this)
  have hrec : Complex.Gamma (3 - w) = (2 - w) * ((1 - w) * Complex.Gamma (1 - w)) := by
    have e1 := Complex.Gamma_add_one (1 - w) hn1
    have e2 := Complex.Gamma_add_one (2 - w) hn2
    rw [show (2 - w) + 1 = 3 - w by ring] at e2
    rw [show (1 - w) + 1 = 2 - w by ring] at e1
    rw [e2, e1]
  have hb1 : 1 / 4 ≤ ‖1 - w‖ := by
    refine h3.trans ?_
    have := Complex.abs_im_le_norm (1 - w)
    simpa using this
  have hb2 : 1 / 4 ≤ ‖2 - w‖ := by
    refine h3.trans ?_
    have := Complex.abs_im_le_norm (2 - w)
    simpa using this
  have hre3 : (3 - w).re = 3 - w.re := by simp
  have hG3 : ‖Complex.Gamma (3 - w)‖ ≤ K :=
    (PI.EF.norm_Gamma_le (by rw [hre3]; linarith)).trans
      (hK _ (by rw [hre3]; linarith) (by rw [hre3]; linarith))
  have hG1 : ‖Complex.Gamma (1 - w)‖ ≤ 16 * K := by
    rw [hrec, norm_mul, norm_mul] at hG3
    have hp := norm_nonneg (Complex.Gamma (1 - w))
    have : (1 / 4) * ((1 / 4) * ‖Complex.Gamma (1 - w)‖) ≤
        ‖2 - w‖ * (‖1 - w‖ * ‖Complex.Gamma (1 - w)‖) := by gcongr
    linarith
  have hs : ‖Complex.sin (Real.pi * w)‖ ≤ Real.exp (Real.pi * |w.im|) := by
    refine (norm_sin_le_exp _).trans (le_of_eq ?_)
    congr 1
    simp [abs_mul, abs_of_pos Real.pi_pos]
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  rw [hinv, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [div_le_iff₀ Real.pi_pos]
  have he := Real.exp_pos (Real.pi * |w.im|)
  calc ‖Complex.Gamma (1 - w)‖ * ‖Complex.sin (Real.pi * w)‖
      ≤ (16 * K) * Real.exp (Real.pi * |w.im|) := by gcongr
    _ = 16 * K * Real.exp (Real.pi * |w.im|) * 1 := by ring
    _ ≤ 16 * K * Real.exp (Real.pi * |w.im|) * Real.pi := by gcongr

/- English proof (translation)
Establish `hG : Complex.Gamma z ≠ 0` using `Complex.Gamma_ne_zero_of_re_pos hz`. Establish `hd : DifferentiableAt ℂ Complex.Gamma z` using `Complex.differentiableAt_Gamma z (fun m h => by`. Use `congrArg Complex.re h` as an intermediate fact. Simplify using `at this`. Establish `h2 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`.

Use the proof step `linarith)`. Establish `h7 : HasDerivAt (fun w => (Complex.Gamma w)⁻¹) (-deriv Complex.Gamma z / Complex.Gamma z ^ 2) z` using `hd.hasDerivAt.inv hG`. Rewrite using `[h7.deriv, Complex.digamma_def, logDeriv_apply]`. Clear the denominators using the available nonvanishing facts.
-/
theorem deriv_inv_Gamma_div {z : ℂ} (hz : 0 < z.re) :
    deriv (fun w => (Complex.Gamma w)⁻¹) z / (Complex.Gamma z)⁻¹ = -digamma z := by
  have hG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have hd : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z (fun m h => by
    have := congrArg Complex.re h
    simp at this
    have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  have h7 : HasDerivAt (fun w => (Complex.Gamma w)⁻¹)
      (-deriv Complex.Gamma z / Complex.Gamma z ^ 2) z := hd.hasDerivAt.inv hG
  rw [h7.deriv, Complex.digamma_def, logDeriv_apply]
  field_simp

/- English proof (translation)
Take `⟨C0, hC0, H⟩` from `GlobalTheory.LWide.disc (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)`. Take `⟨K, hK0, hK⟩` from `exists_Gamma_bound`. Use `set L : ℝ := Real.log (16 * K ^ 2) with hL`. Use `⟨4 * C0 * (1 + |L| + 4 * Real.pi), by positivity, fun z hz1 hz2 hzi => ?_⟩` and prove the remaining obligations. Use `set t : ℝ := |z.im| with ht`.

Establish `ht0 : 0 ≤ t` using `abs_nonneg _`. Use `set F : ℂ → ℂ := fun w => (Complex.Gamma w)⁻¹ with hF`. Establish `hFd : Differentiable ℂ F`. Establish `h` using `Complex.differentiable_one_div_Gamma`. Simplify `h` using `[hF, one_div]`.

Establish `hGz : Complex.Gamma z ≠ 0` using `Complex.Gamma_ne_zero_of_re_pos (by linarith)`. Establish `hFz : F z ≠ 0` using `inv_ne_zero hGz`. Establish `hM : ∀ w, ‖w - z‖ ≤ 1 / 4 → ‖F w‖ ≤ 16 * K * Real.exp (Real.pi * (t + 1))`. Introduce `w hw`. Establish `hre : |w.re - z.re| ≤ 1 / 4`.

Use `(Complex.abs_re_le_norm (w - z)).trans hw` as an intermediate fact. Simplify using `using this`. Establish `him : |w.im - z.im| ≤ 1 / 4`. Use `(Complex.abs_im_le_norm (w - z)).trans hw` as an intermediate fact. Simplify using `using this`.

Establish `hre'` using `abs_le.1 hre`. Establish `h1 : t ≤ |w.im| + 1 / 4`. Use `abs_sub_abs_le_abs_sub z.im w.im` as an intermediate fact. Rewrite `this` using `[abs_sub_comm z.im w.im]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h2 : |w.im| ≤ t + 1 / 4`. Use `abs_sub_abs_le_abs_sub w.im z.im` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `(norm_inv_Gamma_le hK0 hK (by linarith [hre'.1]) (by linarith [hre'.2]) (by linarith)).trans ?_` and prove the remaining obligations. Use `gcongr`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨-, -, h3⟩` from `H F z (1 / 4) (16 * K * Real.exp (Real.pi * (t + 1))) (by norm_num) hFd hFz hM`. Establish `hempty : {w : ℂ | ‖w - z‖ ≤ 1 / 2 * (1 / 4) ∧ F w = 0} = ∅`. Use extensionality with `w`. Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]`.

Introduce `hw`. Establish `hre : |w.re - z.re| ≤ 1 / 2 * (1 / 4)`. Use `(Complex.abs_re_le_norm (w - z)).trans hw` as an intermediate fact. Simplify using `using this`. Establish `hre'` using `abs_le.1 hre`.

Conclude with `inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by linarith [hre'.1]))`. Establish `h4` using `h3 z (by simp) hFz`. Rewrite `h4` using `[hempty, finsum_mem_empty, sub_zero, deriv_inv_Gamma_div (by linarith), norm_neg]`. Establish `hnz : ‖Complex.Gamma z‖ ≤ K` using `(PI.EF.norm_Gamma_le (by linarith)).trans (hK _ (by linarith) (by linarith))`. Establish `hnz0 : 0 < ‖Complex.Gamma z‖` using `norm_pos_iff.2 hGz`.

Establish `hlog : Real.log (16 * K * Real.exp (Real.pi * (t + 1)) / ‖F z‖) ≤ L + Real.pi * (t + 1)`. Establish `he : 16 * K * Real.exp (Real.pi * (t + 1)) / ‖F z‖ = (16 * K * ‖Complex.Gamma z‖) * Real.exp (Real.pi * (t + 1))`. Simplify using `only [hF, norm_inv]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[he, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]`.

Establish `: Real.log (16 * K * ‖Complex.Gamma z‖) ≤ L`. Apply `Real.log_le_log (by positivity)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL' : L ≤ |L|` using `le_abs_self L`.

Establish `hpi` using `Real.pi_pos`. Establish `hfin : (1 / 4) * ‖digamma z‖ ≤ C0 * (1 + |L| + 4 * Real.pi) * (1 + t)`. Use `h4.trans ?_` and prove the remaining obligations. Establish `h5 : 1 + Real.log (16 * K * Real.exp (Real.pi * (t + 1)) / ‖F z‖) ≤ (1 + |L| + 4 * Real.pi) * (1 + t)`. Establish `h6 : 0 ≤ t * (1 + |L|)` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_digamma_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ z.re → z.re ≤ 2 → 1 / 2 ≤ |z.im| →
      ‖digamma z‖ ≤ C * (1 + |z.im|) := by
  obtain ⟨C0, hC0, H⟩ := GlobalTheory.LWide.disc (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨K, hK0, hK⟩ := exists_Gamma_bound
  set L : ℝ := Real.log (16 * K ^ 2) with hL
  refine ⟨4 * C0 * (1 + |L| + 4 * Real.pi), by positivity, fun z hz1 hz2 hzi => ?_⟩
  set t : ℝ := |z.im| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  set F : ℂ → ℂ := fun w => (Complex.Gamma w)⁻¹ with hF
  have hFd : Differentiable ℂ F := by
    have h := Complex.differentiable_one_div_Gamma
    simpa [hF, one_div] using h
  have hGz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hFz : F z ≠ 0 := inv_ne_zero hGz
  have hM : ∀ w, ‖w - z‖ ≤ 1 / 4 → ‖F w‖ ≤ 16 * K * Real.exp (Real.pi * (t + 1)) := by
    intro w hw
    have hre : |w.re - z.re| ≤ 1 / 4 := by
      have := (Complex.abs_re_le_norm (w - z)).trans hw
      simpa using this
    have him : |w.im - z.im| ≤ 1 / 4 := by
      have := (Complex.abs_im_le_norm (w - z)).trans hw
      simpa using this
    have hre' := abs_le.1 hre
    have h1 : t ≤ |w.im| + 1 / 4 := by
      have := abs_sub_abs_le_abs_sub z.im w.im
      rw [abs_sub_comm z.im w.im] at this
      linarith
    have h2 : |w.im| ≤ t + 1 / 4 := by
      have := abs_sub_abs_le_abs_sub w.im z.im
      linarith
    refine (norm_inv_Gamma_le hK0 hK (by linarith [hre'.1]) (by linarith [hre'.2])
      (by linarith)).trans ?_
    gcongr
    linarith
  obtain ⟨-, -, h3⟩ := H F z (1 / 4) (16 * K * Real.exp (Real.pi * (t + 1))) (by norm_num) hFd hFz hM
  have hempty : {w : ℂ | ‖w - z‖ ≤ 1 / 2 * (1 / 4) ∧ F w = 0} = ∅ := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hw
    have hre : |w.re - z.re| ≤ 1 / 2 * (1 / 4) := by
      have := (Complex.abs_re_le_norm (w - z)).trans hw
      simpa using this
    have hre' := abs_le.1 hre
    exact inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by linarith [hre'.1]))
  have h4 := h3 z (by simp) hFz
  rw [hempty, finsum_mem_empty, sub_zero, deriv_inv_Gamma_div (by linarith), norm_neg] at h4
  have hnz : ‖Complex.Gamma z‖ ≤ K :=
    (PI.EF.norm_Gamma_le (by linarith)).trans (hK _ (by linarith) (by linarith))
  have hnz0 : 0 < ‖Complex.Gamma z‖ := norm_pos_iff.2 hGz
  have hlog : Real.log (16 * K * Real.exp (Real.pi * (t + 1)) / ‖F z‖) ≤ L + Real.pi * (t + 1) := by
    have he : 16 * K * Real.exp (Real.pi * (t + 1)) / ‖F z‖ =
        (16 * K * ‖Complex.Gamma z‖) * Real.exp (Real.pi * (t + 1)) := by
      simp only [hF, norm_inv]
      field_simp
    rw [he, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    have : Real.log (16 * K * ‖Complex.Gamma z‖) ≤ L := by
      apply Real.log_le_log (by positivity)
      nlinarith
    linarith
  have hL' : L ≤ |L| := le_abs_self L
  have hpi := Real.pi_pos
  have hfin : (1 / 4) * ‖digamma z‖ ≤ C0 * (1 + |L| + 4 * Real.pi) * (1 + t) := by
    refine h4.trans ?_
    have h5 : 1 + Real.log (16 * K * Real.exp (Real.pi * (t + 1)) / ‖F z‖) ≤
        (1 + |L| + 4 * Real.pi) * (1 + t) := by
      have h6 : 0 ≤ t * (1 + |L|) := by positivity
      nlinarith
    calc _ ≤ C0 * ((1 + |L| + 4 * Real.pi) * (1 + t)) := by gcongr
      _ = _ := by ring
  linarith

end GlobalTheory.CompanionTheory.DigammaStrip
