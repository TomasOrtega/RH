import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.SummableAndAbsTsumSubIntegralLe

open Filter Topology MeasureTheory Set
open scoped Real

namespace GlobalTheory.KroneckerLimit

noncomputable def rowSum (a Y s : ℝ) : ℝ := ∑' n : ℤ, ((a + n) ^ 2 + Y ^ 2) ^ (-s)

/- English proof (translation)
The claim follows from `|rowSum a Y s - betaConst s * Y ^ (1 - 2 * s)| ≤ (Y ^ 2) ^ (-s) := by have := summable_and_abs_tsum_sub_integral_le (f := fun t : ℝ => (t ^ 2 + Y ^ 2) ^ (-s)) (fun t => by positivity) (Continuous.rpow_const (by fun_prop) fun t => Or.inl (by positivity)) (fun u (hu : u ≤ 0) v (hv …`.
-/
theorem rowSum_bound (a : ℝ) {Y s : ℝ} (hY : 0 < Y) (hs : 1 ≤ s) :
    Summable (fun n : ℤ => ((a + n) ^ 2 + Y ^ 2) ^ (-s)) ∧
      |rowSum a Y s - betaConst s * Y ^ (1 - 2 * s)| ≤ (Y ^ 2) ^ (-s) := by
  have := summable_and_abs_tsum_sub_integral_le (f := fun t : ℝ => (t ^ 2 + Y ^ 2) ^ (-s))
    (fun t => by positivity)
    (Continuous.rpow_const (by fun_prop) fun t => Or.inl (by positivity))
    (fun u (hu : u ≤ 0) v (hv : v ≤ 0) huv => Real.rpow_le_rpow_of_nonpos (by positivity)
      (by nlinarith) (by linarith))
    (fun u (hu : 0 ≤ u) v (hv : 0 ≤ v) huv => Real.rpow_le_rpow_of_nonpos (by positivity)
      (by nlinarith) (by linarith))
    (integrable_rpow_sq_add hY hs) a
  rw [integral_rpow_sq_add hY (by linarith)] at this
  simpa [rowSum] using this

/- English proof (translation)
Establish `p1 : 0 ≤ r ^ (-1 : ℝ)` using `by positivity`. Establish `p2 : 0 ≤ r ^ (-2 : ℝ)` using `by positivity`. Break down `le_total r 1 with h | h` into its components or cases. Use `Real.rpow_le_rpow_of_exponent_ge hr h (show (-2 : ℝ) ≤ -s by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `Real.rpow_le_rpow_of_exponent_le h (show -s ≤ (-1 : ℝ) by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rpow_neg_le {r s : ℝ} (hr : 0 < r) (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    r ^ (-s) ≤ r ^ (-1 : ℝ) + r ^ (-2 : ℝ) := by
  have p1 : 0 ≤ r ^ (-1 : ℝ) := by positivity
  have p2 : 0 ≤ r ^ (-2 : ℝ) := by positivity
  rcases le_total r 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge hr h (show (-2 : ℝ) ≤ -s by linarith)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h (show -s ≤ (-1 : ℝ) by linarith)
    linarith

/- English proof (translation)
The claim follows from `Ioc_mem_nhdsGT (by norm_num)`.
-/
theorem eventually_mem_Ioc_one_two : ∀ᶠ s : ℝ in 𝓝[>] 1, 1 < s ∧ s ≤ 2 :=
  Ioc_mem_nhdsGT (by norm_num)

/- English proof (translation)
The claim follows from `((Real.continuousAt_const_rpow hr.ne').comp (f := fun s : ℝ => -s) continuous_neg.continuousAt).tendsto.mono_left nhdsWithin_le_nhds`.
-/
theorem tendsto_rpow_neg {r : ℝ} (hr : 0 < r) :
    Tendsto (fun s : ℝ => r ^ (-s)) (𝓝[>] 1) (𝓝 (r ^ (-1 : ℝ))) :=
  ((Real.continuousAt_const_rpow hr.ne').comp (f := fun s : ℝ => -s)
    continuous_neg.continuousAt).tendsto.mono_left nhdsWithin_le_nhds

/- English proof (translation)
Use `tendsto_tsum_of_dominated_convergence ((rowSum_bound a hY le_rfl).1.add (rowSum_bound a hY one_le_two).1) (fun n => tendsto_rpow_neg (by positivity)) ?_` and prove the remaining obligations. Use `filter_upwards [eventually_mem_Ioc_one_two] with s hs n`. Rewrite using `[Real.norm_of_nonneg (by positivity)]`. Conclude with `rpow_neg_le (by positivity) hs.1.le hs.2`.
-/
theorem tendsto_rowSum (a : ℝ) {Y : ℝ} (hY : 0 < Y) :
    Tendsto (rowSum a Y) (𝓝[>] 1) (𝓝 (rowSum a Y 1)) := by
  refine tendsto_tsum_of_dominated_convergence
    ((rowSum_bound a hY le_rfl).1.add (rowSum_bound a hY one_le_two).1)
    (fun n => tendsto_rpow_neg (by positivity)) ?_
  filter_upwards [eventually_mem_Ioc_one_two] with s hs n
  rw [Real.norm_of_nonneg (by positivity)]
  exact rpow_neg_le (by positivity) hs.1.le hs.2

/- English proof (translation)
Establish `hzZ : z ∈ Complex.integerComplement` using `UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩`. Establish `h1` using `Complex.hasSum_im (summable_cotTerm hzZ).hasSum`. Rewrite `h1` using `[← cot_series_rep' hzZ]`. Use `set f : ℤ → ℝ := fun n => ((z.re + n) ^ 2 + z.im ^ 2) ^ (-1 : ℝ) with hf`. Establish `h2 : HasSum f (rowSum z.re z.im 1)` using `(rowSum_bound z.re hz le_rfl).1.hasSum`.

Establish `h3` using `((hasSum_nat_add_iff' 1).2 h2.nat_add_neg).mul_left (-z.im)`. Establish `him : ∀ n : ℤ, (1 / (z + n)).im = -z.im * f n`. Introduce `n`. Simplify using `[hf, Real.rpow_neg_one, Complex.normSq_apply, div_eq_mul_inv, sq]`. Establish `h4 : (fun n : ℕ => (cotTerm z n).im) = fun n : ℕ => -z.im * (f ((n + 1 : ℕ) : ℤ) + f (-((n + 1 : ℕ) : ℤ)))`.

Use extensionality with `n`. Rewrite using `[mul_add, ← him, ← him, cotTerm, Complex.add_im, add_comm]`. Use `push_cast`. Rewrite using `[sub_eq_add_neg]`. Rewrite `h1` using `[h4]`.

Establish `h5` using `h1.unique h3`. Establish `h6` using `him 0`. Simplify using `only [Int.cast_zero, add_zero] at h6`. Establish `hq : 1 - Complex.exp (2 * π * Complex.I * z) ≠ 0`. Use `UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩` as an intermediate fact.

Introduce `h`. Rewrite `h` using `[sub_eq_zero]`. Simplify using `[← h] at this`. Establish `h7 : π * Complex.cot (π * z) = -Complex.I * (π + 2 * π * (Complex.exp (2 * π * Complex.I * z) / (1 - Complex.exp (2 * π * Complex.I * z))))`. Rewrite using `[Complex.cot_pi_eq_exp_ratio]`.

Generalize the expression as in `Complex.exp (2 * π * Complex.I * z) = w at hq ⊢`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h5` using `[h7, Complex.sub_im, h6]`.

Generalize the expression as in `Complex.exp (2 * π * Complex.I * z) / (1 - Complex.exp (2 * π * Complex.I * z)) = w at h5 ⊢`. Simplify using `at h5`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rowSum_one (z : ℂ) (hz : 0 < z.im) :
    rowSum z.re z.im 1 = π / z.im + 2 * π / z.im *
      (Complex.exp (2 * π * Complex.I * z) / (1 - Complex.exp (2 * π * Complex.I * z))).re := by
  have hzZ : z ∈ Complex.integerComplement :=
    UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩
  have h1 := Complex.hasSum_im (summable_cotTerm hzZ).hasSum
  rw [← cot_series_rep' hzZ] at h1
  set f : ℤ → ℝ := fun n => ((z.re + n) ^ 2 + z.im ^ 2) ^ (-1 : ℝ) with hf
  have h2 : HasSum f (rowSum z.re z.im 1) := (rowSum_bound z.re hz le_rfl).1.hasSum
  have h3 := ((hasSum_nat_add_iff' 1).2 h2.nat_add_neg).mul_left (-z.im)
  have him : ∀ n : ℤ, (1 / (z + n)).im = -z.im * f n := by
    intro n
    simp [hf, Real.rpow_neg_one, Complex.normSq_apply, div_eq_mul_inv, sq]
  have h4 : (fun n : ℕ => (cotTerm z n).im)
      = fun n : ℕ => -z.im * (f ((n + 1 : ℕ) : ℤ) + f (-((n + 1 : ℕ) : ℤ))) := by
    ext n
    rw [mul_add, ← him, ← him, cotTerm, Complex.add_im, add_comm]
    push_cast
    rw [sub_eq_add_neg]
  rw [h4] at h1
  have h5 := h1.unique h3
  have h6 := him 0
  simp only [Int.cast_zero, add_zero] at h6
  have hq : 1 - Complex.exp (2 * π * Complex.I * z) ≠ 0 := by
    have := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩
    intro h
    rw [sub_eq_zero] at h
    simp [← h] at this
  have h7 : π * Complex.cot (π * z) = -Complex.I * (π + 2 * π *
      (Complex.exp (2 * π * Complex.I * z) / (1 - Complex.exp (2 * π * Complex.I * z)))) := by
    rw [Complex.cot_pi_eq_exp_ratio]
    generalize Complex.exp (2 * π * Complex.I * z) = w at hq ⊢
    field_simp
    rw [Complex.I_sq]
    ring
  rw [h7, Complex.sub_im, h6] at h5
  generalize Complex.exp (2 * π * Complex.I * z) / (1 - Complex.exp (2 * π * Complex.I * z)) = w
    at h5 ⊢
  simp at h5
  field_simp
  linarith

/- English proof (translation)
Use `set F : ℕ × ℕ → ℂ := fun p => (q ^ (p.1 + 1)) ^ (p.2 + 1) / (p.2 + 1) with hF`. Establish `hq0` using `norm_nonneg q`. Establish `hpow : ∀ k : ℕ, ‖q ^ (k + 1)‖ < 1` using `fun k => by`. Rewrite using `[norm_pow]; exact pow_lt_one₀ hq0 hq (by omega)`. Establish `hs : Summable F`.

Establish `g` using `summable_geometric_of_lt_one hq0 hq`. Use `.of_norm_bounded (g.mul_of_nonneg g (fun _ => by positivity) fun _ => by positivity) ?_` and prove the remaining obligations. Introduce and unpack `⟨k, m⟩`. Simplify using `only [hF, norm_div, norm_pow, ← pow_mul, ← pow_add]`. Establish `: (1 : ℝ) ≤ ‖(m + 1 : ℂ)‖`.

Rewrite using `[show (m + 1 : ℂ) = ((m + 1 : ℕ) : ℂ) by push_cast; rfl, Complex.norm_natCast]`. Use `push_cast`. Combine the linear relations using `[(Nat.cast_nonneg m : (0:ℝ) ≤ m)]`. Use `(div_le_self (by positivity) this).trans ?_` and prove the remaining obligations. Conclude with `pow_le_pow_of_le_one hq0 hq.le (by nlinarith)`.

Establish `hA : HasSum (fun k : ℕ => -Complex.log (1 - q ^ (k + 1))) (∑' p, F p)`. Use `hs.hasSum.prod_fiberwise fun k => ?_` and prove the remaining obligations. Simplify `Complex.hasSum_taylorSeries_neg_log' (hpow k)` using `[hF]`. Establish `hB : HasSum (fun m : ℕ => q ^ (m + 1) / (1 - q ^ (m + 1)) / (m + 1)) (∑' p, F p)`. Use `((Equiv.prodComm ℕ ℕ).hasSum_iff.2 hs.hasSum).prod_fiberwise fun m => ?_` and prove the remaining obligations.

Use `((hasSum_geometric_of_norm_lt_one (hpow m)).mul_left (q ^ (m + 1))).div_const (m + 1 : ℂ)` as an intermediate fact. Rewrite `this` using `[← div_eq_mul_inv]`. Use `this.congr_fun fun k => ?_` and prove the remaining obligations. Simplify using `only [hF, Function.comp_apply, Equiv.prodComm_apply, Prod.swap_prod_mk]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hne : ∀ k : ℕ, 1 - q ^ (k + 1) ≠ 0` using `fun k h => by`. Use `hpow k` as an intermediate fact. Rewrite `h` using `[sub_eq_zero]`. Simplify using `[← h] at this`. Establish `hA' : HasSum (fun k : ℕ => Complex.log (1 - q ^ (k + 1))) (-∑' p, F p)`.

Simplify using `using hA.neg`. Rewrite using `[← Complex.cexp_tsum_eq_tprod hne hA'.summable, hA'.tsum_eq, Complex.norm_exp, Real.log_exp, Complex.neg_re, neg_neg]`. Use `Complex.hasSum_re hB using 2 with m` and compare the differences between its conclusion and the goal. Rewrite using `[show (m + 1 : ℂ) = ((m + 1 : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re]`.
-/
theorem hasSum_lambert {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => (q ^ (m + 1) / (1 - q ^ (m + 1))).re / (m + 1))
      (-Real.log ‖∏' k : ℕ, (1 - q ^ (k + 1))‖) := by
  set F : ℕ × ℕ → ℂ := fun p => (q ^ (p.1 + 1)) ^ (p.2 + 1) / (p.2 + 1) with hF
  have hq0 := norm_nonneg q
  have hpow : ∀ k : ℕ, ‖q ^ (k + 1)‖ < 1 := fun k => by
    rw [norm_pow]; exact pow_lt_one₀ hq0 hq (by omega)
  have hs : Summable F := by
    have g := summable_geometric_of_lt_one hq0 hq
    refine .of_norm_bounded (g.mul_of_nonneg g (fun _ => by positivity) fun _ => by positivity) ?_
    rintro ⟨k, m⟩
    simp only [hF, norm_div, norm_pow, ← pow_mul, ← pow_add]
    have : (1 : ℝ) ≤ ‖(m + 1 : ℂ)‖ := by
      rw [show (m + 1 : ℂ) = ((m + 1 : ℕ) : ℂ) by push_cast; rfl, Complex.norm_natCast]
      push_cast; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    refine (div_le_self (by positivity) this).trans ?_
    exact pow_le_pow_of_le_one hq0 hq.le (by nlinarith)
  have hA : HasSum (fun k : ℕ => -Complex.log (1 - q ^ (k + 1))) (∑' p, F p) := by
    refine hs.hasSum.prod_fiberwise fun k => ?_
    simpa [hF] using Complex.hasSum_taylorSeries_neg_log' (hpow k)
  have hB : HasSum (fun m : ℕ => q ^ (m + 1) / (1 - q ^ (m + 1)) / (m + 1)) (∑' p, F p) := by
    refine ((Equiv.prodComm ℕ ℕ).hasSum_iff.2 hs.hasSum).prod_fiberwise fun m => ?_
    have := ((hasSum_geometric_of_norm_lt_one (hpow m)).mul_left (q ^ (m + 1))).div_const
      (m + 1 : ℂ)
    rw [← div_eq_mul_inv] at this
    refine this.congr_fun fun k => ?_
    simp only [hF, Function.comp_apply, Equiv.prodComm_apply, Prod.swap_prod_mk]
    ring
  have hne : ∀ k : ℕ, 1 - q ^ (k + 1) ≠ 0 := fun k h => by
    have := hpow k
    rw [sub_eq_zero] at h
    simp [← h] at this
  have hA' : HasSum (fun k : ℕ => Complex.log (1 - q ^ (k + 1))) (-∑' p, F p) := by
    simpa using hA.neg
  rw [← Complex.cexp_tsum_eq_tprod hne hA'.summable, hA'.tsum_eq, Complex.norm_exp, Real.log_exp,
    Complex.neg_re, neg_neg]
  convert Complex.hasSum_re hB using 2 with m
  rw [show (m + 1 : ℂ) = ((m + 1 : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re]

/- English proof (translation)
Establish `h0 : Tendsto (fun s : ℝ => 2 * s - 1) (𝓝[>] 1) (𝓝[>] 1)`. Use `tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Establish `: Continuous fun s : ℝ => 2 * s - 1` using `by fun_prop`. Use `(this.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi 1))` as an intermediate fact. Evaluate the numerical expressions using `at this`.

Conclude with `this`. Use `filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s) show 1 < 2 * s - 1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `(Complex.continuous_re.tendsto _).comp (ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right.comp h0)`. Rewrite `h1` using `[Complex.ofReal_re]`.

Use `h1.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)`. Simplify using `only [Function.comp_apply]`. Use `(congrArg Complex.re ?_).trans (Complex.ofReal_re _)` and prove the remaining obligations. Rewrite using `[zeta_eq_tsum_one_div_nat_add_one_cpow (by rw [Complex.ofReal_re]; linarith), Complex.ofReal_sub (∑' _, _), Complex.ofReal_tsum]`.

Use `congr 1`. Use `congr 1 with n`. Rewrite using `[Complex.ofReal_cpow (by positivity), one_div, ← Complex.cpow_neg]`. Apply the tactic sequence `congr 1 <;> push_cast <;> ring`. Use `push_cast`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tendsto_zeta_two_mul_sub_one :
    Tendsto (fun s : ℝ => (∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s)) - 1 / (2 * (s - 1))) (𝓝[>] 1)
      (𝓝 Real.eulerMascheroniConstant) := by
  have h0 : Tendsto (fun s : ℝ => 2 * s - 1) (𝓝[>] 1) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Continuous fun s : ℝ => 2 * s - 1 := by fun_prop
      have := (this.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi 1))
      norm_num at this
      exact this
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      show 1 < 2 * s - 1
      linarith
  have h1 := (Complex.continuous_re.tendsto _).comp
    (ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right.comp h0)
  rw [Complex.ofReal_re] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  simp only [Function.comp_apply]
  refine (congrArg Complex.re ?_).trans (Complex.ofReal_re _)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by rw [Complex.ofReal_re]; linarith),
    Complex.ofReal_sub (∑' _, _), Complex.ofReal_tsum]
  congr 1
  · congr 1 with n
    rw [Complex.ofReal_cpow (by positivity), one_div, ← Complex.cpow_neg]
    congr 1 <;> push_cast <;> ring
  · push_cast
    congr 1
    ring

/- English proof (translation)
Use `set g : ℝ → ℝ := fun s => betaConst s * y ^ (1 - s) with hg`. Establish `hg1 : g 1 = π` using `by simp [hg, betaConst_one]`. Establish `hd : HasDerivAt g (-2 * π * Real.log 2 - π * Real.log y) 1`. Establish `h1 : HasDerivAt (fun s : ℝ => y ^ (1 - s)) _ 1` using `((hasDerivAt_id' (1 : ℝ)).const_sub 1).const_rpow hy`. Use `(hasDerivAt_betaConst_one.mul h1).congr_deriv ?_` and prove the remaining obligations.

Simplify using `[betaConst_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `t1 : Tendsto g (𝓝[>] 1) (𝓝 π)` using `hg1 ▸ hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds`. Establish `t2` using `(hasDerivAt_iff_tendsto_slope.1 hd).mono_left (nhdsWithin_mono _ (show Ioi (1 : ℝ) ⊆ {1}ᶜ from fun _ h => ne_of_gt h))`. Establish `t3` using `((t1.const_mul 2).mul tendsto_zeta_two_mul_sub_one).add t2`.

Use `t3.congr' ?_ using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)`. Establish `: s - 1 ≠ 0` using `by linarith`. Rewrite using `[slope_def_field, hg1]`.

Express the relevant statement in the definitionally equal form `_ = 2 * g s * _ - _`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tendsto_integral_part {y : ℝ} (hy : 0 < y) :
    Tendsto (fun s : ℝ => 2 * (betaConst s * y ^ (1 - s)) * (∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s))
      - π / (s - 1)) (𝓝[>] 1)
      (𝓝 (2 * π * (Real.eulerMascheroniConstant - Real.log 2) - π * Real.log y)) := by
  set g : ℝ → ℝ := fun s => betaConst s * y ^ (1 - s) with hg
  have hg1 : g 1 = π := by simp [hg, betaConst_one]
  have hd : HasDerivAt g (-2 * π * Real.log 2 - π * Real.log y) 1 := by
    have h1 : HasDerivAt (fun s : ℝ => y ^ (1 - s)) _ 1 :=
      ((hasDerivAt_id' (1 : ℝ)).const_sub 1).const_rpow hy
    refine (hasDerivAt_betaConst_one.mul h1).congr_deriv ?_
    simp [betaConst_one]
    ring
  have t1 : Tendsto g (𝓝[>] 1) (𝓝 π) :=
    hg1 ▸ hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have t2 := (hasDerivAt_iff_tendsto_slope.1 hd).mono_left
    (nhdsWithin_mono _ (show Ioi (1 : ℝ) ⊆ {1}ᶜ from fun _ h => ne_of_gt h))
  have t3 := ((t1.const_mul 2).mul tendsto_zeta_two_mul_sub_one).add t2
  convert t3.congr' ?_ using 2
  · ring
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    have : s - 1 ≠ 0 := by linarith
    rw [slope_def_field, hg1]
    change _ = 2 * g s * _ - _
    field_simp
    ring

/- English proof (translation)
Use `(Real.summable_abs_int_rpow (b := 2 * s) (by linarith)).congr fun n => ?_` and prove the remaining obligations. Rewrite using `[show -(2 * s) = ((2 : ℕ) : ℝ) * (-s) by push_cast; ring, Real.rpow_natCast_mul (abs_nonneg _)]`. Simplify using the standard rewrite rules.
-/
theorem summable_zero_row {s : ℝ} (hs : 1 ≤ s) :
    Summable (fun n : ℤ => (((0 : ℝ) + n) ^ 2 + 0 ^ 2) ^ (-s)) := by
  refine (Real.summable_abs_int_rpow (b := 2 * s) (by linarith)).congr fun n => ?_
  rw [show -(2 * s) = ((2 : ℕ) : ℝ) * (-s) by push_cast; ring, Real.rpow_natCast_mul (abs_nonneg _)]
  simp

/- English proof (translation)
Establish `h1 : rowSum 0 0 1 = π ^ 2 / 3`. Establish `h2` using `(summable_zero_row le_rfl).hasSum.nat_add_neg`. Establish `h3` using `hasSum_zeta_two.mul_left 2`. Use `h2.unique (h3.congr_fun fun n => by simp [Real.rpow_neg_one]; ring)` as an intermediate fact. Simplify using `at this`.

Simplify using `[rowSum, this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h1]`. Use `tendsto_tsum_of_dominated_convergence (summable_zero_row le_rfl) (fun n => ?_) ?_` and prove the remaining obligations. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases.

Use `tendsto_const_nhds.congr' ?_ filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)` and prove the remaining obligations. Simplify using `[Real.zero_rpow (show -s ≠ 0 by linarith)]`. Conclude with `tendsto_rpow_neg (by simp; positivity)`. Use `filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s) n`. Rewrite using `[Real.norm_of_nonneg (by positivity)]`.

Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[Real.zero_rpow (show -s ≠ 0 by linarith)]`. Use `Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)` and prove the remaining obligations. Establish `: (1 : ℤ) ≤ n ^ 2` using `(by positivity : (0 : ℤ) < n ^ 2)`. Simplify using `using (by exact_mod_cast this : (1 : ℝ) ≤ (n : ℝ) ^ 2)`.
-/
theorem tendsto_zero_row : Tendsto (rowSum 0 0) (𝓝[>] 1) (𝓝 (π ^ 2 / 3)) := by
  have h1 : rowSum 0 0 1 = π ^ 2 / 3 := by
    have h2 := (summable_zero_row le_rfl).hasSum.nat_add_neg
    have h3 := hasSum_zeta_two.mul_left 2
    have := h2.unique (h3.congr_fun fun n => by simp [Real.rpow_neg_one]; ring)
    simp at this
    simp [rowSum, this]
    ring
  rw [← h1]
  refine tendsto_tsum_of_dominated_convergence (summable_zero_row le_rfl) (fun n => ?_) ?_
  · rcases eq_or_ne n 0 with rfl | hn
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      simp [Real.zero_rpow (show -s ≠ 0 by linarith)]
    · exact tendsto_rpow_neg (by simp; positivity)
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s) n
    rw [Real.norm_of_nonneg (by positivity)]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow (show -s ≠ 0 by linarith)]
    · refine Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)
      have : (1 : ℤ) ≤ n ^ 2 := (by positivity : (0 : ℤ) < n ^ 2)
      simpa using (by exact_mod_cast this : (1 : ℝ) ≤ (n : ℝ) ^ 2)

noncomputable def rowError (x y : ℝ) (m : ℕ) (s : ℝ) : ℝ :=
  rowSum ((m + 1) * x) ((m + 1) * y) s - betaConst s * ((m + 1) * y) ^ (1 - 2 * s)

/- English proof (translation)
Use `((summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (show -(2 * s) < -1 by linarith))).mul_right ((y ^ 2) ^ (-s))` as an intermediate fact. Use `this.congr fun m => ?_` and prove the remaining obligations. Rewrite using `[mul_pow, Real.mul_rpow (by positivity) (by positivity), show -(2 * s) = ((2 : ℕ) : ℝ) * (-s) by push_cast; ring, Real.rpow_natCast_mul (by positivity)]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem summable_sq_rpow {y s : ℝ} (hy : 0 < y) (hs : 1 ≤ s) :
    Summable fun m : ℕ => (((m + 1) * y) ^ 2) ^ (-s) := by
  have := ((summable_nat_add_iff 1).2
    (Real.summable_nat_rpow.2 (show -(2 * s) < -1 by linarith))).mul_right ((y ^ 2) ^ (-s))
  refine this.congr fun m => ?_
  rw [mul_pow, Real.mul_rpow (by positivity) (by positivity),
    show -(2 * s) = ((2 : ℕ) : ℝ) * (-s) by push_cast; ring, Real.rpow_natCast_mul (by positivity)]
  push_cast
  rfl

/- English proof (translation)
The claim follows from `.of_norm_bounded (summable_sq_rpow hy hs) fun m => (rowSum_bound _ (by positivity) hs).2`.
-/
theorem summable_rowError (x : ℝ) {y s : ℝ} (hy : 0 < y) (hs : 1 ≤ s) :
    Summable fun m => rowError x y m s :=
  .of_norm_bounded (summable_sq_rpow hy hs) fun m =>
    (rowSum_bound _ (by positivity) hs).2

/- English proof (translation)
Use `tendsto_tsum_of_dominated_convergence ((summable_sq_rpow hy le_rfl).add (summable_sq_rpow hy one_le_two)) (fun m => ?_) ?_` and prove the remaining obligations. Establish `hY : 0 < ((m : ℝ) + 1) * y` using `by positivity`. Use `(tendsto_rowSum _ hY).sub (Tendsto.mono_left ?_ nhdsWithin_le_nhds)` and prove the remaining obligations. Use `hasDerivAt_betaConst_one.continuousAt.tendsto.mul ?_` and prove the remaining obligations. Conclude with `((Real.continuousAt_const_rpow hY.ne').comp (f := fun s : ℝ => 1 - 2 * s) (by fun_prop)).tendsto`.

Use `filter_upwards [eventually_mem_Ioc_one_two] with s hs m`. Conclude with `(rowSum_bound _ (by positivity) hs.1.le).2.trans (rpow_neg_le (by positivity) hs.1.le hs.2)`.
-/
theorem tendsto_tsum_rowError (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun s => ∑' m, rowError x y m s) (𝓝[>] 1) (𝓝 (∑' m, rowError x y m 1)) := by
  refine tendsto_tsum_of_dominated_convergence
    ((summable_sq_rpow hy le_rfl).add (summable_sq_rpow hy one_le_two)) (fun m => ?_) ?_
  · have hY : 0 < ((m : ℝ) + 1) * y := by positivity
    refine (tendsto_rowSum _ hY).sub (Tendsto.mono_left ?_ nhdsWithin_le_nhds)
    refine hasDerivAt_betaConst_one.continuousAt.tendsto.mul ?_
    exact ((Real.continuousAt_const_rpow hY.ne').comp (f := fun s : ℝ => 1 - 2 * s)
      (by fun_prop)).tendsto
  · filter_upwards [eventually_mem_Ioc_one_two] with s hs m
    exact (rowSum_bound _ (by positivity) hs.1.le).2.trans (rpow_neg_le (by positivity) hs.1.le hs.2)

/- English proof (translation)
Establish `hq` using `UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩`. Establish `h` using `(hasSum_lambert hq).mul_left (2 * π / z.im)`. Simplify using `only [ModularForm.eta_q_eq_pow]`. Rewrite using `[neg_mul, ← mul_neg]`. Use `HasSum.tsum_eq (h.congr_fun fun m => ?_)` and prove the remaining obligations.

Establish `hY : 0 < ((m : ℝ) + 1) * z.im` using `by positivity`. Use `rowSum_one ((m + 1) * z) (by simpa using hY)` as an intermediate fact. Rewrite `this` using `[show 2 * π * Complex.I * ((m + 1) * z) = ((m + 1 : ℕ) : ℂ) * (2 * π * Complex.I * z) by push_cast; ring, Complex.exp_nat_mul]`. Establish `e1 : ((m + 1) * z).re = (m + 1) * z.re` using `by simp`. Establish `e2 : ((m + 1) * z).im = (m + 1) * z.im` using `by simp`.

Rewrite `this` using `[e1, e2]`. Rewrite using `[rowError, this, betaConst_one, show (1 : ℝ) - 2 * 1 = -1 by norm_num, Real.rpow_neg_one]`. Simplify using `only`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tsum_rowError_one (z : ℂ) (hz : 0 < z.im) :
    ∑' m, rowError z.re z.im m 1
      = -(2 * π / z.im) * Real.log ‖∏' k : ℕ, (1 - ModularForm.eta_q k z)‖ := by
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩
  have h := (hasSum_lambert hq).mul_left (2 * π / z.im)
  simp only [ModularForm.eta_q_eq_pow]
  rw [neg_mul, ← mul_neg]
  refine HasSum.tsum_eq (h.congr_fun fun m => ?_)
  have hY : 0 < ((m : ℝ) + 1) * z.im := by positivity
  have := rowSum_one ((m + 1) * z) (by simpa using hY)
  rw [show 2 * π * Complex.I * ((m + 1) * z) = ((m + 1 : ℕ) : ℂ) * (2 * π * Complex.I * z) by
    push_cast; ring, Complex.exp_nat_mul] at this
  have e1 : ((m + 1) * z).re = (m + 1) * z.re := by simp
  have e2 : ((m + 1) * z).im = (m + 1) * z.im := by simp
  rw [e1, e2] at this
  rw [rowError, this, betaConst_one, show (1 : ℝ) - 2 * 1 = -1 by norm_num, Real.rpow_neg_one]
  simp only
  field_simp
  ring

/- English proof (translation)
Rewrite using `[rowSum, rowSum, ← (Equiv.neg ℤ).tsum_eq]`. Use `congr 1 with n`. Use `congr 1`. Simplify using `only [Equiv.neg_apply, Int.cast_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rowSum_neg (a Y s : ℝ) : rowSum (-a) (-Y) s = rowSum a Y s := by
  rw [rowSum, rowSum, ← (Equiv.neg ℤ).tsum_eq]
  congr 1 with n
  congr 1
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring

/- English proof (translation)
Break down `eq_or_ne m 0 with rfl | hm` into its components or cases. Simplify using `using summable_zero_row hs`. Use `(rowSum_bound (m * x) (Y := |m * y|) (by positivity) hs).1` as an intermediate fact. Simplify `this` using `only [sq_abs]`.
-/
theorem summable_row (x : ℝ) {y s : ℝ} (hy : 0 < y) (hs : 1 ≤ s) (m : ℤ) :
    Summable fun n : ℤ => (((m : ℝ) * x + n) ^ 2 + (m * y) ^ 2) ^ (-s) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simpa using summable_zero_row hs
  · have := (rowSum_bound (m * x) (Y := |m * y|) (by positivity) hs).1
    simpa only [sq_abs] using this

/- English proof (translation)
Establish `h1 : Summable fun n : ℕ => (n + 1 : ℝ) ^ (1 - 2 * s)`. Conclude with `(summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (show 1 - 2 * s < -1 by linarith))` after adjusting the coercions. Establish `h2 : HasSum (fun m : ℕ => rowSum ((m + 1) * x) ((m + 1) * y) s) ((∑' m, rowError x y m s) + (betaConst s * y ^ (1 - 2 * s)) * ∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s))`. Use `((summable_rowError x hy hs.le).hasSum.add (h1.hasSum.mul_left _)).congr_fun fun m => ?_` and prove the remaining obligations. Rewrite using `[rowError, Real.mul_rpow (by positivity) hy.le]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `HasSum.of_add_one_of_neg_add_one (f := fun m : ℤ => rowSum (m * x) (m * y) s) (h2.congr_fun fun m => by push_cast; rfl) (h2.congr_fun fun m => by push_cast; rw [neg_mul, neg_mul, rowSum_neg])`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasSum_rows (x : ℝ) {y s : ℝ} (hy : 0 < y) (hs : 1 < s) :
    HasSum (fun m : ℤ => rowSum (m * x) (m * y) s)
      (rowSum 0 0 s + 2 * (∑' m, rowError x y m s)
        + 2 * (betaConst s * y ^ (1 - 2 * s)) * ∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s)) := by
  have h1 : Summable fun n : ℕ => (n + 1 : ℝ) ^ (1 - 2 * s) := by
    exact_mod_cast (summable_nat_add_iff 1).2
      (Real.summable_nat_rpow.2 (show 1 - 2 * s < -1 by linarith))
  have h2 : HasSum (fun m : ℕ => rowSum ((m + 1) * x) ((m + 1) * y) s)
      ((∑' m, rowError x y m s)
        + (betaConst s * y ^ (1 - 2 * s)) * ∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s)) := by
    refine ((summable_rowError x hy hs.le).hasSum.add (h1.hasSum.mul_left _)).congr_fun fun m => ?_
    rw [rowError, Real.mul_rpow (by positivity) hy.le]
    ring
  have h3 := HasSum.of_add_one_of_neg_add_one (f := fun m : ℤ => rowSum (m * x) (m * y) s)
    (h2.congr_fun fun m => by push_cast; rfl)
    (h2.congr_fun fun m => by push_cast; rw [neg_mul, neg_mul, rowSum_neg])
  convert h3 using 1
  simp
  ring

/- English proof (translation)
Establish `h : Summable fun p : ℤ × ℤ => (((p.1 : ℝ) * x + p.2) ^ 2 + (p.1 * y) ^ 2) ^ (-s)` using `(summable_prod_of_nonneg fun p => by positivity).2 ⟨summable_row x hy hs.le, (hasSum_rows x hy hs).summable⟩`. Rewrite using `[← (hasSum_rows x hy hs).tsum_eq]`. Conclude with `h.tsum_prod ▸ h.hasSum`.
-/
theorem hasSum_lattice (x : ℝ) {y s : ℝ} (hy : 0 < y) (hs : 1 < s) :
    HasSum (fun p : ℤ × ℤ => (((p.1 : ℝ) * x + p.2) ^ 2 + (p.1 * y) ^ 2) ^ (-s))
      (rowSum 0 0 s + 2 * (∑' m, rowError x y m s)
        + 2 * (betaConst s * y ^ (1 - 2 * s)) * ∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s)) := by
  have h : Summable fun p : ℤ × ℤ => (((p.1 : ℝ) * x + p.2) ^ 2 + (p.1 * y) ^ 2) ^ (-s) :=
    (summable_prod_of_nonneg fun p => by positivity).2
      ⟨summable_row x hy hs.le, (hasSum_rows x hy hs).summable⟩
  rw [← (hasSum_rows x hy hs).tsum_eq]
  exact h.tsum_prod ▸ h.hasSum

/- English proof (translation)
Rewrite using `[Real.log_pow, ModularForm.eta, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (Function.Periodic.qParam_ne_zero _)) (norm_ne_zero_iff.2 (ModularForm.eta_tprod_ne_zero hz)), Function.Periodic.norm_qParam, Real.log_exp]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_norm_eta_sq (z : ℂ) (hz : 0 < z.im) :
    Real.log (‖ModularForm.eta z‖ ^ 2)
      = -(π * z.im / 6) + 2 * Real.log ‖∏' k : ℕ, (1 - ModularForm.eta_q k z)‖ := by
  rw [Real.log_pow, ModularForm.eta, norm_mul, Real.log_mul
    (norm_ne_zero_iff.2 (Function.Periodic.qParam_ne_zero _))
    (norm_ne_zero_iff.2 (ModularForm.eta_tprod_ne_zero hz)), Function.Periodic.norm_qParam,
    Real.log_exp]
  push_cast
  ring

/- English proof (translation)
Establish `hy` using `τ.im_pos`. Establish `h` using `(hasSum_lattice τ.re hy hs).mul_left (τ.im ^ s)`. Establish `e : τ.im ^ (1 - s) = τ.im ^ s * τ.im ^ (1 - 2 * s)`. Rewrite using `[← Real.rpow_add hy]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `h'` using `(hasSum_subtype_iff_of_support_subset (s := {p : ℤ × ℤ | p ≠ 0}) (by`. Introduce `p hp h0`. Apply `hp` to reduce the goal to its premises. Simplify using `[h0, Real.zero_rpow (show -s ≠ 0 by linarith)])).2 h`.

Rewrite `h'` using `[mul_add (τ.im ^ s), show ∀ a b c d : ℝ, a * (2 * (b * c) * d) = 2 * (b * (a * c)) * d by intros; ring, ← e]`. Use `h'.congr_fun (fun p => ?_)` and prove the remaining obligations. Rewrite using `[show 2 * s = ((2 : ℕ) : ℝ) * s by norm_num, Real.rpow_natCast_mul (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply, Function.comp_apply, Real.rpow_neg (by positivity), div_eq_mul_inv]`. Simplify using `[sq]`.
-/
theorem hasSum_eisenstein (τ : UpperHalfPlane) {s : ℝ} (hs : 1 < s) :
    HasSum (fun p : {p : ℤ × ℤ // p ≠ 0} =>
        τ.im ^ s / ‖(p.1.1 * τ + p.1.2 : ℂ)‖ ^ (2 * s))
      (τ.im ^ s * (rowSum 0 0 s + 2 * (∑' m, rowError τ.re τ.im m s))
        + 2 * (betaConst s * τ.im ^ (1 - s)) * ∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s)) := by
  have hy := τ.im_pos
  have h := (hasSum_lattice τ.re hy hs).mul_left (τ.im ^ s)
  have e : τ.im ^ (1 - s) = τ.im ^ s * τ.im ^ (1 - 2 * s) := by
    rw [← Real.rpow_add hy]; congr 1; ring
  have h' := (hasSum_subtype_iff_of_support_subset (s := {p : ℤ × ℤ | p ≠ 0}) (by
    intro p hp h0
    apply hp
    simp [h0, Real.zero_rpow (show -s ≠ 0 by linarith)])).2 h
  rw [mul_add (τ.im ^ s), show ∀ a b c d : ℝ, a * (2 * (b * c) * d) = 2 * (b * (a * c)) * d by
    intros; ring, ← e] at h'
  refine h'.congr_fun (fun p => ?_)
  · rw [show 2 * s = ((2 : ℕ) : ℝ) * s by norm_num, Real.rpow_natCast_mul (norm_nonneg _),
      Complex.sq_norm, Complex.normSq_apply, Function.comp_apply,
      Real.rpow_neg (by positivity), div_eq_mul_inv]
    simp [sq]

end GlobalTheory.KroneckerLimit

namespace GlobalTheory

open KroneckerLimit

/- English proof (translation)
The claim follows from `(hasSum_eisenstein τ hs).summable`.
-/
theorem summable_realEisenstein (τ : UpperHalfPlane) {s : ℝ} (hs : 1 < s) :
    Summable fun p : {p : ℤ × ℤ // p ≠ 0} => τ.im ^ s / ‖(p.1.1 * τ + p.1.2 : ℂ)‖ ^ (2 * s) :=
  (hasSum_eisenstein τ hs).summable

/- English proof (translation)
Establish `hy` using `τ.im_pos`. Establish `t0 : Tendsto (fun s : ℝ => τ.im ^ s) (𝓝[>] 1) (𝓝 τ.im)`. Simplify using `using (Real.continuousAt_const_rpow (b := 1) hy.ne').tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 1))`. Establish `t1` using `(t0.mul (tendsto_zero_row.add ((tendsto_tsum_rowError τ.re hy).const_mul 2))).add (tendsto_integral_part hy)`. Establish `e1` using `tsum_rowError_one τ hy`.

Establish `e2` using `log_norm_eta_sq τ hy`. Rewrite `e1` using `[UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]`. Rewrite `e2` using `[UpperHalfPlane.coe_im]`. Use `t1.congr' ?_ using 2` and compare the differences between its conclusion and the goal. Rewrite using `[e1, e2]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)`. Rewrite using `[(hasSum_eisenstein τ hs).tsum_eq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tendsto_realEisenstein_sub_pole (τ : UpperHalfPlane) :
    Tendsto (fun s : ℝ =>
        (∑' p : {p : ℤ × ℤ // p ≠ 0}, τ.im ^ s / ‖(p.1.1 * τ + p.1.2 : ℂ)‖ ^ (2 * s))
          - π / (s - 1)) (𝓝[>] 1)
      (𝓝 (2 * π * (Real.eulerMascheroniConstant - Real.log 2) - π * Real.log τ.im
        - 2 * π * Real.log (‖ModularForm.eta τ‖ ^ 2))) := by
  have hy := τ.im_pos
  have t0 : Tendsto (fun s : ℝ => τ.im ^ s) (𝓝[>] 1) (𝓝 τ.im) := by
    simpa using (Real.continuousAt_const_rpow (b := 1) hy.ne').tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 1))
  have t1 := (t0.mul (tendsto_zero_row.add ((tendsto_tsum_rowError τ.re hy).const_mul 2))).add
    (tendsto_integral_part hy)
  have e1 := tsum_rowError_one τ hy
  have e2 := log_norm_eta_sq τ hy
  rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at e1
  rw [UpperHalfPlane.coe_im] at e2
  convert t1.congr' ?_ using 2
  · rw [e1, e2]
    field_simp
    ring
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    rw [(hasSum_eisenstein τ hs).tsum_eq]
    ring

end GlobalTheory
