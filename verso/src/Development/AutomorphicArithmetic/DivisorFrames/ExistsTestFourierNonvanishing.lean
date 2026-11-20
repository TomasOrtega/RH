import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
import Development.AutomorphicArithmetic.DivisorFrames.GaussianFourierConjPower
open MeasureTheory FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

/- English proof (translation)
Rewrite using `[integrable_fun_norm_addHaar (volume : Measure ℂ) (f := fun r : ℝ => r ^ p * Real.exp (-Real.pi * r ^ 2))]`. Establish `h` using `integrableOn_rpow_mul_exp_neg_mul_sq Real.pi_pos (s := p + 1) (by linarith)`. Use `h.congr_fun (fun r hr => ?_) measurableSet_Ioi` and prove the remaining obligations. Establish `hr' : (0 : ℝ) < r` using `hr`. Simplify using `only [Complex.finrank_real_complex, smul_eq_mul]`.

Rewrite using `[Real.rpow_add_one hr'.ne']`. Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma rad_int (p : ℝ) (hp : -2 < p) :
    Integrable (fun s : ℂ => ‖s‖ ^ p * Real.exp (-Real.pi * ‖s‖ ^ 2)) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ)
    (f := fun r : ℝ => r ^ p * Real.exp (-Real.pi * r ^ 2))]
  have h := integrableOn_rpow_mul_exp_neg_mul_sq Real.pi_pos (s := p + 1) (by linarith)
  refine h.congr_fun (fun r hr => ?_) measurableSet_Ioi
  have hr' : (0 : ℝ) < r := hr
  simp only [Complex.finrank_real_complex, smul_eq_mul]
  rw [Real.rpow_add_one hr'.ne']
  norm_num
  ring

/- English proof (translation)
Use `rad_int (m : ℝ) (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)` as an intermediate fact. Simplify `this` using `only [Real.rpow_natCast]`.
-/
private lemma nat_int (m : ℕ) :
    Integrable (fun s : ℂ => ‖s‖ ^ m * Real.exp (-Real.pi * ‖s‖ ^ 2)) := by
  have := rad_int (m : ℝ) (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
  simpa only [Real.rpow_natCast] using this

private noncomputable def gk (k : ℕ) (s : ℂ) : ℂ :=
  (starRingEnd ℂ s) ^ k * Complex.exp (-(Real.pi : ℂ) * (‖s‖ : ℂ) ^ 2)

/- English proof (translation)
Use `push_cast`. Both sides reduce to the same expression.
-/
private lemma cexp_eq (s : ℂ) : Complex.exp (-(Real.pi : ℂ) * (‖s‖ : ℂ) ^ 2)
    = ((Real.exp (-Real.pi * ‖s‖ ^ 2) : ℝ) : ℂ) := by
  push_cast; rfl

/- English proof (translation)
Use `Integrable.mono' (nat_int k) ?_ (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Use `Complex.continuous_conj` as an intermediate fact. Apply `Continuous.aestronglyMeasurable` to reduce the goal to its premises. Unfold `gk`. Use `fun_prop`.

Rewrite using `[gk, cexp_eq, norm_mul, norm_pow, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]`.
-/
private lemma gk_int (k : ℕ) : Integrable (gk k) := by
  refine Integrable.mono' (nat_int k) ?_ (Filter.Eventually.of_forall fun s => ?_)
  · have := Complex.continuous_conj
    apply Continuous.aestronglyMeasurable
    unfold gk
    fun_prop
  · rw [gk, cexp_eq, norm_mul, norm_pow, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]

/- English proof (translation)
Distinguish the cases in `hs : s = 0`. Substitute `hs` using the available equality. Simplify using `[gk, hk.ne']`. Establish `h : (‖s‖ : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.2 hs`. Establish `h2 : starRingEnd ℂ s * (s / (‖s‖ : ℂ)) = (‖s‖ : ℂ)`.

Rewrite using `[← mul_div_assoc, mul_comm, Complex.mul_conj']`. Clear the denominators using the available nonvanishing facts. Rewrite using `[gk, cexp_eq, zpow_natCast, Complex.ofReal_mul, Complex.ofReal_pow, pow_add]`. Establish `h3` using `congrArg (· ^ k) h2`. Simplify using `only [mul_pow] at h3`.

Rewrite using `[← h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma gk_wt (k e : ℕ) (hk : 0 < k) (s : ℂ) :
    gk k s * ((s / (‖s‖ : ℂ)) ^ (k : ℤ) * (‖s‖ : ℂ) ^ (2 * e))
      = ((‖s‖ ^ (k + 2 * e) * Real.exp (-Real.pi * ‖s‖ ^ 2) : ℝ) : ℂ) := by
  by_cases hs : s = 0
  · subst hs
    simp [gk, hk.ne']
  · have h : (‖s‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hs
    have h2 : starRingEnd ℂ s * (s / (‖s‖ : ℂ)) = (‖s‖ : ℂ) := by
      rw [← mul_div_assoc, mul_comm, Complex.mul_conj']
      field_simp
    rw [gk, cexp_eq, zpow_natCast, Complex.ofReal_mul, Complex.ofReal_pow, pow_add]
    have h3 := congrArg (· ^ k) h2
    simp only [mul_pow] at h3
    rw [← h3]
    ring

/- English proof (translation)
Use `integral_pos_of_integrable_nonneg_nonzero (x := 1) (by fun_prop) (nat_int m) (fun s => by positivity) ?_` and prove the remaining obligations. Use `Real.exp_pos (-Real.pi)` as an intermediate fact. Simplify using the standard rewrite rules.
-/
private lemma rad_pos (m : ℕ) :
    0 < ∫ s : ℂ, ‖s‖ ^ m * Real.exp (-Real.pi * ‖s‖ ^ 2) := by
  refine integral_pos_of_integrable_nonneg_nonzero (x := 1) (by fun_prop) (nat_int m)
    (fun s => by positivity) ?_
  have := Real.exp_pos (-Real.pi)
  simp

/- English proof (translation)
Establish `hp : (-2 : ℝ) < (k : ℝ) - ((2 * e + 2 : ℕ) : ℝ)`. Establish `: ((2 * e : ℕ) : ℝ) < k` using `by exact_mod_cast hk`. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Integrable.mono' (rad_int _ hp) ?_ ?_` and prove the remaining obligations.

Apply `Measurable.aestronglyMeasurable` to reduce the goal to its premises. Establish `h : Measurable fun s : ℂ => (‖s‖ : ℂ)` using `Complex.measurable_ofReal.comp measurable_norm`. Use `Measurable.mul (by fun_prop) (Measurable.inv ?_)` and prove the remaining obligations. Conclude with `(((measurable_id.div h).pow_const _).mul (h.pow_const _)).mul (h.pow_const _)`. Establish `h0 : ∀ᵐ y : ℂ, y ≠ 0`.

Simplify using `[ae_iff]`. Use `filter_upwards [h0] with y hy`. Establish `h : 0 < ‖y‖` using `norm_pos_iff.2 hy`. Rewrite using `[cexp_eq, Real.rpow_sub h, Real.rpow_natCast, Real.rpow_natCast]`. Simplify using `only [norm_mul, norm_inv, norm_pow, norm_zpow, norm_div, Complex.norm_real, norm_norm, norm_neg, Complex.norm_I, one_mul, div_self h.ne', one_zpow, Real.norm_of_nonneg (Real.exp_pos _).le]`.

Apply `le_of_eq` to reduce the goal to its premises. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`.
-/
private lemma dual_int (k e : ℕ) (hk : 2 * e < k) :
    Integrable (fun y : ℂ => ((-Complex.I * y) ^ k * Complex.exp (-(Real.pi : ℂ) * (‖y‖ : ℂ) ^ 2)) *
      (((y / (‖y‖ : ℂ)) ^ (k : ℤ) * (‖y‖ : ℂ) ^ (2 * e)) * (‖y‖ : ℂ) ^ 2)⁻¹) := by
  have hp : (-2 : ℝ) < (k : ℝ) - ((2 * e + 2 : ℕ) : ℝ) := by
    have : ((2 * e : ℕ) : ℝ) < k := by exact_mod_cast hk
    push_cast at this ⊢
    linarith
  refine Integrable.mono' (rad_int _ hp) ?_ ?_
  · apply Measurable.aestronglyMeasurable
    have h : Measurable fun s : ℂ => (‖s‖ : ℂ) := Complex.measurable_ofReal.comp measurable_norm
    refine Measurable.mul (by fun_prop) (Measurable.inv ?_)
    exact (((measurable_id.div h).pow_const _).mul (h.pow_const _)).mul (h.pow_const _)
  · have h0 : ∀ᵐ y : ℂ, y ≠ 0 := by
      simp [ae_iff]
    filter_upwards [h0] with y hy
    have h : 0 < ‖y‖ := norm_pos_iff.2 hy
    rw [cexp_eq, Real.rpow_sub h, Real.rpow_natCast, Real.rpow_natCast]
    simp only [norm_mul, norm_inv, norm_pow, norm_zpow, norm_div, Complex.norm_real, norm_norm,
      norm_neg, Complex.norm_I, one_mul, div_self h.ne', one_zpow,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    apply le_of_eq
    field_simp
    try ring

/- English proof (translation)
Introduce `ι _ κ e hκ`. Take `⟨k, rfl⟩ : ∃ k : ι → ℕ, κ = fun w => (k w : ℤ)` from `⟨fun w => (κ w).toNat, funext fun w => by have := hκ w; simp only; omega⟩`. Establish `hk : ∀ w, 2 * e < k w` using `fun w => by have := hκ w; simp only at this; omega`. Establish `hw : (fun s : ι → ℂ => (∏ w, gk (k w) (s w)) * wt (fun w => (k w : ℤ)) e s) = fun s => ∏ w, ((‖s w‖ ^ (k w + 2 * e) * Real.exp (-Real.pi * ‖s w‖ ^ 2) : ℝ) : ℂ)`. Use function extensionality and compare the values at `s`.

Rewrite using `[wt, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun w _ => gk_wt _ _ (by have := hk w; omega) _`. Use `⟨fun s => ∏ w, gk (k w) (s w), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Integrable.fintype_prod (f := fun w => gk (k w)) fun w => gk_int _`. Rewrite using `[hw]`.

Conclude with `Integrable.fintype_prod (f := fun w (s : ℂ) => ((‖s‖ ^ (k w + 2 * e) * Real.exp (-Real.pi * ‖s‖ ^ 2) : ℝ) : ℂ)) fun w => (nat_int _).ofReal`. Establish `hF : (fun y : ι → ℂ => FT (fun s => ∏ w, gk (k w) (s w)) y * dwt (fun w => (k w : ℤ)) e y) = fun y => ∏ w, ((-Complex.I * y w) ^ k w * Complex.exp (-(Real.pi : ℂ) * (‖y w‖ : ℂ) ^ 2)) * (((y w / (‖y w‖ : ℂ)) ^ (k w : ℤ) * (‖y w‖ : ℂ) ^ (2 * e)) * (‖y w‖ : ℂ) ^ 2)⁻¹`. Use function extensionality and compare the values at `y`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_mul_distrib (g := fun w => (‖y w‖ : ℂ) ^ 2)]`. Use `congr 1`.

Simplify using `only [← UpperTheory.gaussian_fourier_conj_power]`. Rewrite using `[← integral_fintype_prod_volume_eq_prod (fun w (s : ℂ) => (starRingEnd ℂ s) ^ k w * Complex.exp (-(Real.pi : ℂ) * (‖s‖ : ℂ) ^ 2) * Complex.exp (-(2 * Real.pi * Complex.I) * (((s * y w).re : ℝ) : ℂ))), FT]`. Use `congr 1`. Use function extensionality and compare the values at `s`. Rewrite using `[Finset.prod_mul_distrib (g := fun w => Complex.exp (-(2 * Real.pi * Complex.I) * (((s w * y w).re : ℝ) : ℂ))), ← Complex.exp_sum, ec, Complex.re_sum, Complex.ofReal_sum, Finset.mul_sum]`.

Both sides reduce to the same expression. Simplify using `only [dwt, wt, nm, Complex.ofReal_prod, Complex.ofReal_pow]`. Rewrite using `[hF]`. Conclude with `Integrable.fintype_prod (f := fun w (y : ℂ) => ((-Complex.I * y) ^ k w * Complex.exp (-(Real.pi : ℂ) * (‖y‖ : ℂ) ^ 2)) * (((y / (‖y‖ : ℂ)) ^ (k w : ℤ) * (‖y‖ : ℂ) ^ (2 * e)) * (‖y‖ : ℂ) ^ 2)⁻¹) fun w => dual_int _ _ (hk w)`. Rewrite using `[hw, integral_fintype_prod_volume_eq_prod (fun w (s : ℂ) => ((‖s‖ ^ (k w + 2 * e) * Real.exp (-Real.pi * ‖s‖ ^ 2) : ℝ) : ℂ))]`.

Use `Finset.prod_ne_zero_iff.2 fun w _ => ?_` and prove the remaining obligations. Rewrite using `[integral_complex_ofReal]`. Conclude with `(rad_pos _).ne'` after adjusting the coercions.
-/
theorem UpperTheory.exists_test_fourier_nonvanishing :
    ∀ {ι : Type} [Fintype ι] (κ : ι → ℤ) (e : ℕ), (∀ w, 2 * (e : ℤ) < κ w) → ∃ h : (ι → ℂ) → ℂ, Integrable h ∧
        Integrable (fun s => h s * wt κ e s) ∧ Integrable (fun y => FT h y * dwt κ e y) ∧ ∫ s, h s * wt κ e s ≠ 0 := by
  intro ι _ κ e hκ
  obtain ⟨k, rfl⟩ : ∃ k : ι → ℕ, κ = fun w => (k w : ℤ) :=
    ⟨fun w => (κ w).toNat, funext fun w => by have := hκ w; simp only; omega⟩
  have hk : ∀ w, 2 * e < k w := fun w => by have := hκ w; simp only at this; omega
  have hw : (fun s : ι → ℂ => (∏ w, gk (k w) (s w)) * wt (fun w => (k w : ℤ)) e s)
      = fun s => ∏ w, ((‖s w‖ ^ (k w + 2 * e) * Real.exp (-Real.pi * ‖s w‖ ^ 2) : ℝ) : ℂ) := by
    funext s
    rw [wt, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ => gk_wt _ _ (by have := hk w; omega) _
  refine ⟨fun s => ∏ w, gk (k w) (s w), ?_, ?_, ?_, ?_⟩
  · exact Integrable.fintype_prod (f := fun w => gk (k w)) fun w => gk_int _
  · rw [hw]
    exact Integrable.fintype_prod
      (f := fun w (s : ℂ) => ((‖s‖ ^ (k w + 2 * e) * Real.exp (-Real.pi * ‖s‖ ^ 2) : ℝ) : ℂ))
      fun w => (nat_int _).ofReal
  · have hF : (fun y : ι → ℂ => FT (fun s => ∏ w, gk (k w) (s w)) y * dwt (fun w => (k w : ℤ)) e y)
        = fun y => ∏ w, ((-Complex.I * y w) ^ k w * Complex.exp (-(Real.pi : ℂ) * (‖y w‖ : ℂ) ^ 2)) *
      (((y w / (‖y w‖ : ℂ)) ^ (k w : ℤ) * (‖y w‖ : ℂ) ^ (2 * e)) * (‖y w‖ : ℂ) ^ 2)⁻¹ := by
      funext y
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_mul_distrib (g := fun w => (‖y w‖ : ℂ) ^ 2)]
      congr 1
      · simp only [← UpperTheory.gaussian_fourier_conj_power]
        rw [← integral_fintype_prod_volume_eq_prod (fun w (s : ℂ) => (starRingEnd ℂ s) ^ k w *
          Complex.exp (-(Real.pi : ℂ) * (‖s‖ : ℂ) ^ 2) *
          Complex.exp (-(2 * Real.pi * Complex.I) * (((s * y w).re : ℝ) : ℂ))), FT]
        congr 1
        funext s
        rw [Finset.prod_mul_distrib (g := fun w => Complex.exp (-(2 * Real.pi * Complex.I) * (((s w * y w).re : ℝ) : ℂ))),
          ← Complex.exp_sum, ec, Complex.re_sum, Complex.ofReal_sum, Finset.mul_sum]
        rfl
      · simp only [dwt, wt, nm, Complex.ofReal_prod, Complex.ofReal_pow]
    rw [hF]
    exact Integrable.fintype_prod
      (f := fun w (y : ℂ) => ((-Complex.I * y) ^ k w * Complex.exp (-(Real.pi : ℂ) * (‖y‖ : ℂ) ^ 2)) *
      (((y / (‖y‖ : ℂ)) ^ (k w : ℤ) * (‖y‖ : ℂ) ^ (2 * e)) * (‖y‖ : ℂ) ^ 2)⁻¹)
      fun w => dual_int _ _ (hk w)
  · rw [hw, integral_fintype_prod_volume_eq_prod
      (fun w (s : ℂ) => ((‖s‖ ^ (k w + 2 * e) * Real.exp (-Real.pi * ‖s‖ ^ 2) : ℝ) : ℂ))]
    refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
    rw [integral_complex_ofReal]
    exact_mod_cast (rad_pos _).ne'
