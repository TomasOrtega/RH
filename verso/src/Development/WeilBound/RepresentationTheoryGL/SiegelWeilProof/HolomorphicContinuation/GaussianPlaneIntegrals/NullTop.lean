import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt

noncomputable section

open MeasureTheory MvPolynomial Filter Topology

namespace PositivityTheory.Rg.Sw.FFTSteps

variable {m n : ℕ}

/- English proof (translation)
Unfold `gs`. Rewrite using `[Complex.ofReal_exp, Complex.ofReal_neg]`.
-/
theorem gs_eq (c : ℝ) (x : Fin m → Fin n → ℂ) :
    gs c x = ((Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) : ℝ) : ℂ) := by
  unfold gs
  rw [Complex.ofReal_exp, Complex.ofReal_neg]

/- English proof (translation)
Repeatedly rewrite using `[gs_eq]`. Use `fun_prop`.
-/
theorem continuous_gs (c : ℝ) : Continuous fun x : Fin m → Fin n → ℂ => gs c x := by
  simp_rw [gs_eq]
  fun_prop

/- English proof (translation)
Rewrite using `[gs_eq, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]`.
-/
theorem norm_gs (c : ℝ) (x : Fin m → Fin n → ℂ) :
    ‖gs c x‖ = Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) := by
  rw [gs_eq, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

/- English proof (translation)
Simplify using `only [gs, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gs_half (c : ℝ) (x : Fin m → Fin n → ℂ) : gs c x = gs (c / 2) x * gs (c / 2) x := by
  simp only [gs, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/- English proof (translation)
Establish `h` using `GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (c : ℂ)) (by simpa using hc) 0 0`. Use `h.norm.congr (ae_of_all _ fun z => ?_)` and prove the remaining obligations. Simplify using `only [zero_mul, add_zero, Complex.norm_exp]`. Use `norm_cast`. Rewrite using `[neg_mul]`.
-/
theorem integrable_gauss1 {c : ℝ} (hc : 0 < c) : Integrable (fun z : ℂ => Real.exp (-(c * ‖z‖ ^ 2))) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (c : ℂ)) (by simpa using hc) 0 0
  refine h.norm.congr (ae_of_all _ fun z => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  norm_cast
  rw [neg_mul]

/- English proof (translation)
Simplify using `only [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]`.
-/
theorem exp_sum_sum (c : ℝ) (x : Fin m → Fin n → ℂ) :
    Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) = ∏ a, ∏ i, Real.exp (-(c * ‖x a i‖ ^ 2)) := by
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]

/- English proof (translation)
Conclude with `Integrable.fintype_prod (f := fun _ z => Real.exp (-(c * ‖z‖ ^ 2))) (fun _ => integrable_gauss1 hc)`.
-/
theorem integrable_gs_row {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : Fin n → ℂ => ∏ i, Real.exp (-(c * ‖y i‖ ^ 2))) := by
  exact Integrable.fintype_prod (f := fun _ z => Real.exp (-(c * ‖z‖ ^ 2))) (fun _ => integrable_gauss1 hc)

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `h` using `Integrable.fintype_prod (ι := Fin m) (E := Fin n → ℂ) (μ := fun _ => (volume : Measure (Fin n → ℂ))) (f := fun _ y => ∏ i, Real.exp (-(c * ‖y i‖ ^ 2))) (fun _ => integrable_gs_row hc)`. Conclude with `h`.
-/
theorem integrable_gs_prod {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Fin m → Fin n → ℂ => ∏ a, ∏ i, Real.exp (-(c * ‖x a i‖ ^ 2))) := by
  have h := Integrable.fintype_prod (ι := Fin m) (E := Fin n → ℂ) (μ := fun _ => (volume : Measure (Fin n → ℂ)))
    (f := fun _ y => ∏ i, Real.exp (-(c * ‖y i‖ ^ 2))) (fun _ => integrable_gs_row hc)
  exact h

/- English proof (translation)
Conclude with `(integrable_gs_prod hc).congr (ae_of_all _ fun x => (exp_sum_sum c x).symm)`.
-/
theorem integrable_gs_re {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Fin m → Fin n → ℂ => Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2))) := by
  exact (integrable_gs_prod hc).congr (ae_of_all _ fun x => (exp_sum_sum c x).symm)

/- English proof (translation)
Conclude with `(integrable_gs_re hc).ofReal.congr (ae_of_all _ fun x => (gs_eq c x).symm)`.
-/
theorem integrable_gs {c : ℝ} (hc : 0 < c) : Integrable (fun x : Fin m → Fin n → ℂ => gs c x) := by
  exact (integrable_gs_re hc).ofReal.congr (ae_of_all _ fun x => (gs_eq c x).symm)

/- English proof (translation)
Establish `hS0 : 0 ≤ S` using `le_trans (sq_nonneg r) hS`. Establish `h1 : 1 + a * S ≤ Real.exp (a * S)`. Use `Real.add_one_le_exp (a * S)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hinv : 0 ≤ 1 / a` using `by positivity`.

Establish `haS : 0 ≤ a * S` using `mul_nonneg ha.le hS0`. Establish `hprod : (1 + 1 / a) * (1 + a * S) = 1 + a * S + 1 / a + S`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : r ≤ (1 + 1 / a) * (1 + a * S)`.

Rewrite using `[hprod]`. Use polynomial arithmetic with `[sq_nonneg (r - 1)]`. Establish `h3 : r ≤ (1 + 1 / a) * Real.exp (a * S)`. Establish `: 0 ≤ 1 + 1 / a` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]`. Conclude with `h3`.
-/
theorem bound_aux {a r S : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hS : r ^ 2 ≤ S) :
    r * Real.exp (-(a * S)) ≤ 1 + 1 / a := by
  have hS0 : 0 ≤ S := le_trans (sq_nonneg r) hS
  have h1 : 1 + a * S ≤ Real.exp (a * S) := by
    have := Real.add_one_le_exp (a * S)
    linarith
  have hinv : 0 ≤ 1 / a := by positivity
  have haS : 0 ≤ a * S := mul_nonneg ha.le hS0
  have hprod : (1 + 1 / a) * (1 + a * S) = 1 + a * S + 1 / a + S := by
    field_simp
    ring
  have h2 : r ≤ (1 + 1 / a) * (1 + a * S) := by
    rw [hprod]
    nlinarith [sq_nonneg (r - 1)]
  have h3 : r ≤ (1 + 1 / a) * Real.exp (a * S) := by
    have : 0 ≤ 1 + 1 / a := by positivity
    nlinarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  exact h3

/- English proof (translation)
Establish `h1 : ‖x a i‖ ^ 2 ≤ ∑ j, ‖x a j‖ ^ 2` using `Finset.single_le_sum (f := fun j => ‖x a j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)`. Establish `h2 : ∑ j, ‖x a j‖ ^ 2 ≤ ∑ b, ∑ j, ‖x b j‖ ^ 2` using `Finset.single_le_sum (f := fun b => ∑ j, ‖x b j‖ ^ 2) (fun b _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ a)`. Conclude with `h1.trans h2`.
-/
theorem sq_le_sum_sum (x : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) :
    ‖x a i‖ ^ 2 ≤ ∑ a, ∑ i, ‖x a i‖ ^ 2 := by
  have h1 : ‖x a i‖ ^ 2 ≤ ∑ j, ‖x a j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖x a j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : ∑ j, ‖x a j‖ ^ 2 ≤ ∑ b, ∑ j, ‖x b j‖ ^ 2 :=
    Finset.single_le_sum (f := fun b => ∑ j, ‖x b j‖ ^ 2)
      (fun b _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ a)
  exact h1.trans h2

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Introduce `c hc`. Establish `e : (fun x => evX (C a : PX m n) x * gs c x) = fun x => a * gs c x`. Use function extensionality and compare the values at `x`.

Simplify using `[evX]`. Rewrite using `[e]`. Conclude with `(integrable_gs hc).const_mul a`. Consider the case `add p q hp hq`. Introduce `c hc`.

Establish `e : (fun x => evX (p + q) x * gs c x) = fun x => evX p x * gs c x + evX q x * gs c x`. Use function extensionality and compare the values at `x`. Simplify using `only [evX, map_add, add_mul]`. Rewrite using `[e]`. Conclude with `(hp hc).add (hq hc)`.

Consider the case `mul_X p k hp`. Introduce `c hc`. Establish `hc2 : 0 < c / 2` using `by positivity`. Establish `e : (fun x => evX (p * X k) x * gs c x) = fun x => ((if k.2.2 = true then star (x k.1 k.2.1) else x k.1 k.2.1) * gs (c / 2) x) * (evX p x * gs (c / 2) x)`. Use function extensionality and compare the values at `x`.

Simplify using `only [evX, map_mul, eval_X]`. Rewrite using `[gs_half c x]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `(hp hc2).bdd_mul (c := 1 + 1 / (c / 2)) ?_ ?_` and prove the remaining obligations.

Use `Continuous.aestronglyMeasurable (Continuous.mul ?_ (continuous_gs _))` and prove the remaining obligations. Distinguish the cases in `hk : k.2.2 = true`. Simplify using `only [hk, if_true] fun_prop`. Simplify using `only [hk, Bool.false_eq_true, if_false] fun_prop`. Use `ae_of_all _ fun x => ?_` and prove the remaining obligations.

Apply the tactic sequence `have hn : ‖(if k.2.2 = true then star (x k.1 k.2.1) else x k.1 k.2.1)‖ = ‖x k.1 k.2.1‖ := by split_ifs <;> simp`. Rewrite using `[norm_mul, norm_gs, hn]`. Conclude with `bound_aux hc2 (norm_nonneg _) (sq_le_sum_sum x k.1 k.2.1)`.
-/
theorem integrable_evX_gs (P : PX m n) : ∀ {c : ℝ}, 0 < c → Integrable (fun x => evX P x * gs c x) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro c hc
    have e : (fun x => evX (C a : PX m n) x * gs c x) = fun x => a * gs c x := by
      funext x
      simp [evX]
    rw [e]
    exact (integrable_gs hc).const_mul a
  | add p q hp hq =>
    intro c hc
    have e : (fun x => evX (p + q) x * gs c x) = fun x => evX p x * gs c x + evX q x * gs c x := by
      funext x
      simp only [evX, map_add, add_mul]
    rw [e]
    exact (hp hc).add (hq hc)
  | mul_X p k hp =>
    intro c hc
    have hc2 : 0 < c / 2 := by positivity
    have e : (fun x => evX (p * X k) x * gs c x) = fun x =>
        ((if k.2.2 = true then star (x k.1 k.2.1) else x k.1 k.2.1) * gs (c / 2) x) *
          (evX p x * gs (c / 2) x) := by
      funext x
      simp only [evX, map_mul, eval_X]
      rw [gs_half c x]
      ring
    rw [e]
    refine (hp hc2).bdd_mul (c := 1 + 1 / (c / 2)) ?_ ?_
    · refine Continuous.aestronglyMeasurable (Continuous.mul ?_ (continuous_gs _))
      by_cases hk : k.2.2 = true
      · simp only [hk, if_true]
        fun_prop
      · simp only [hk, Bool.false_eq_true, if_false]
        fun_prop
    · refine ae_of_all _ fun x => ?_
      have hn : ‖(if k.2.2 = true then star (x k.1 k.2.1) else x k.1 k.2.1)‖ = ‖x k.1 k.2.1‖ := by
        split_ifs <;> simp
      rw [norm_mul, norm_gs, hn]
      exact bound_aux hc2 (norm_nonneg _) (sq_le_sum_sum x k.1 k.2.1)

/- English proof (translation)
Unfold `mom`. Establish `h : ∀ x, evX ((R1 + R2) * P) x * gs c x = evX (R1 * P) x * gs c x + evX (R2 * P) x * gs c x`. Introduce `x`. Simplify using `only [evX, add_mul, map_add]`. Repeatedly rewrite using `[h]`.

Conclude with `integral_add (integrable_evX_gs _ hc) (integrable_evX_gs _ hc)`.
-/
theorem mom_add {c : ℝ} (hc : 0 < c) (R1 R2 P : PX m n) :
    mom c ((R1 + R2) * P) = mom c (R1 * P) + mom c (R2 * P) := by
  unfold mom
  have h : ∀ x, evX ((R1 + R2) * P) x * gs c x = evX (R1 * P) x * gs c x + evX (R2 * P) x * gs c x := by
    intro x
    simp only [evX, add_mul, map_add]
  simp_rw [h]
  exact integral_add (integrable_evX_gs _ hc) (integrable_evX_gs _ hc)

/- English proof (translation)
Unfold `mom`. Establish `h : ∀ x, evX ((a • R) * P) x * gs c x = a * (evX (R * P) x * gs c x)`. Introduce `x`. Simplify using `only [evX, smul_eq_C_mul, map_mul, eval_C]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[h]`. Conclude with `integral_const_mul a _`.
-/
theorem mom_smul (c : ℝ) (a : ℂ) (R P : PX m n) : mom c ((a • R) * P) = a * mom c (R * P) := by
  unfold mom
  have h : ∀ x, evX ((a • R) * P) x * gs c x = a * (evX (R * P) x * gs c x) := by
    intro x
    simp only [evX, smul_eq_C_mul, map_mul, eval_C]
    ring
  simp_rw [h]
  exact integral_const_mul a _

/- English proof (translation)
Simplify using `[mom, evX]`.
-/
theorem mom_zero (c : ℝ) (P : PX m n) : mom c (0 * P) = 0 := by
  simp [mom, evX]

/- English proof (translation)
Simplify using `only [evX, map_sum, map_mul, MvPolynomial.eval_C, Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX]`.
-/
theorem evX_ell (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    evX (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) x = (b * gramX ε x).trace := by
  simp only [evX, map_sum, map_mul, MvPolynomial.eval_C, Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX]

/- English proof (translation)
Use `Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ ?_ ?_` and prove the remaining obligations. Conclude with `Subalgebra.algebraMap_mem _ (b i j)`. Conclude with `Algebra.subset_adjoin ⟨(j, i), rfl⟩`.
-/
theorem ell_mem (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ∈
      Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n)) := by
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ ?_ ?_
  · exact Subalgebra.algebraMap_mem _ (b i j)
  · exact Algebra.subset_adjoin ⟨(j, i), rfl⟩

/- English proof (translation)
Unfold `mom`. Use `congr 1`. Use extensionality with `x`. Establish `e : evX ((∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ^ k * P) x = (evX (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) x) ^ k * evX P x`. Simplify using `only [evX, map_mul, map_pow]`.

Rewrite using `[e, evX_ell]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mom_ellpow (ε : Fin m → Bool) (c : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) (P : PX m n) :
    mom c ((∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ^ k * P) =
      ∫ x : Fin m → Fin n → ℂ, evX P x * gs c x * ((b * gramX ε x).trace) ^ k := by
  unfold mom
  congr 1
  ext x
  have e : evX ((∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ^ k * P) x =
      (evX (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) x) ^ k * evX P x := by
    simp only [evX, map_mul, map_pow]
  rw [e, evX_ell]
  ring

/- English proof (translation)
The claim follows from `isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const`.
-/
theorem strip_open (δ : ℝ) : IsOpen {z : ℂ | |z.im| < δ} :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

/- English proof (translation)
Establish `e : {z : ℂ | |z.im| < δ} = Complex.imLm ⁻¹' Set.Ioo (-δ) δ`. Use extensionality with `z`. Simplify using `[abs_lt]`. Rewrite using `[e]`. Conclude with `((convex_Ioo (-δ) δ).linear_preimage Complex.imLm).isPreconnected`.
-/
theorem strip_conn (δ : ℝ) : IsPreconnected {z : ℂ | |z.im| < δ} := by
  have e : {z : ℂ | |z.im| < δ} = Complex.imLm ⁻¹' Set.Ioo (-δ) δ := by
    ext z; simp [abs_lt]
  rw [e]
  exact ((convex_Ioo (-δ) δ).linear_preimage Complex.imLm).isPreconnected

/- English proof (translation)
Introduce `m n ε c t hc ht P`. Prove the components needed by the constructor for the conclusion. Introduce `hN b hb`. Take `⟨δ, hδ, hd, hre, hder⟩` from `hS m n ε c t hc P b hb`. Use `set F : ℂ → ℂ := fun z => ∫ x : Fin m → Fin n → ℂ, evX P x * gs c x * Complex.exp (Complex.I * ↑t * z * (b * gramX ε x).trace) with hF`.

Establish `hball : Metric.ball (0:ℂ) δ ⊆ {z : ℂ | |z.im| < δ}`. Introduce `z hz`. Simplify using `only [Metric.mem_ball, dist_zero_right] at hz`. Conclude with `lt_of_le_of_lt (Complex.abs_im_le_norm z) hz`. Establish `hzero : ∀ k, iteratedDeriv k F 0 = 0`.

Introduce `k`. Rewrite using `[hder k, ← mom_ellpow, hN _ (Subalgebra.pow_mem _ (ell_mem ε b) k), mul_zero]`. Establish `hloc : F =ᶠ[𝓝 0] 0` using `by filter_upwards [Metric.ball_mem_nhds (0:ℂ) hδ] with z hz`. Rewrite using `[← Complex.taylorSeries_eq_on_ball' hz (hd.mono hball)]`. Simplify using `[hzero]`.

Establish `han : AnalyticOnNhd ℂ F {z : ℂ | |z.im| < δ}` using `hd.analyticOnNhd (strip_open δ)`. Establish `h0 : (0:ℂ) ∈ {z : ℂ | |z.im| < δ}` using `by simpa using hδ`. Establish `h1 : (1:ℂ) ∈ {z : ℂ | |z.im| < δ}` using `by simpa using hδ`. Establish `hF1` using `han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (strip_conn δ) h0 hloc h1`. Establish `e1` using `hre 1 (by simp)`.

Rewrite `e1` using `[one_smul]`. Rewrite using `[← e1]`. Conclude with `hF1`. Introduce `hall R hR`. Establish `hR' : R ∈ Submodule.span ℂ {R : PX m n | ∃ (b : Matrix (Fin n) (Fin n) ℂ) (k : ℕ), b.IsHermitian ∧ R = (∑ i : Fin n, ∑ j : Fin n, C (b i j) * Qp ε j i) ^ k}`.

Rewrite using `[← hP m n ε]`. Conclude with `hR`. Use `clear hR`. Proceed by induction on `hR' using Submodule.span_induction with`. Consider the case `mem R hmem`.

Take `⟨b, k, hb, rfl⟩` from `hmem`. Take `⟨δ, hδ, hd, hre, hder⟩` from `hS m n ε c t hc P b hb`. Use `set F : ℂ → ℂ := fun z => ∫ x : Fin m → Fin n → ℂ, evX P x * gs c x * Complex.exp (Complex.I * ↑t * z * (b * gramX ε x).trace) with hF`. Establish `han : AnalyticOnNhd ℂ F {z : ℂ | |z.im| < δ}` using `hd.analyticOnNhd (strip_open δ)`. Establish `h0 : (0:ℂ) ∈ {z : ℂ | |z.im| < δ}` using `by simpa using hδ`.

Establish `hreal : ∀ r : ℝ, F r = 0`. Introduce `r`. Rewrite using `[show F r = _ from hre (r:ℂ) (Complex.ofReal_im r)]`. Apply `hall` to reduce the goal to its premises. Unfold `Matrix.IsHermitian`.

Rewrite using `[Matrix.conjTranspose_smul, hb.eq, Complex.star_def, Complex.conj_ofReal]`. Establish `hfreq : ∃ᶠ z in 𝓝[≠] (0:ℂ), F z = 0`. Establish `hc0 : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝 0) (𝓝 0)`. Simplify using `using Complex.continuous_ofReal.tendsto (0:ℝ)`. Establish `hT : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0)`.

Use `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hc0.mono_left nhdsWithin_le_nhds) ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with r hr`. Simplify using `using hr`. Conclude with `hT.frequently (Frequently.of_forall hreal)`. Establish `hloc` using `((han 0 h0).frequently_zero_iff_eventually_zero).mp hfreq`.

Establish `hk` using `hder k`. Rewrite `hk` using `[Filter.EventuallyEq.iteratedDeriv_eq k (hloc : F =ᶠ[𝓝 0] 0)]`. Simplify using `at hk`. Rewrite using `[mom_ellpow]`. Conclude with `hk.resolve_left (fun h => ht h.1)`.

Consider the case `zero => exact mom_zero c P`. Consider the case `add x y _ _ hx hy => rw [mom_add hc, hx, hy, add_zero]`. Consider the case `smul a x _ hx => rw [mom_smul, hx, mul_zero]`.
-/
theorem nullIff_of (hS : SecLine) (hP : PowSpan) : NullIff := by
  intro m n ε c t hc ht P
  constructor
  · intro hN b hb
    obtain ⟨δ, hδ, hd, hre, hder⟩ := hS m n ε c t hc P b hb
    set F : ℂ → ℂ := fun z => ∫ x : Fin m → Fin n → ℂ,
      evX P x * gs c x * Complex.exp (Complex.I * ↑t * z * (b * gramX ε x).trace) with hF
    have hball : Metric.ball (0:ℂ) δ ⊆ {z : ℂ | |z.im| < δ} := by
      intro z hz
      simp only [Metric.mem_ball, dist_zero_right] at hz
      exact lt_of_le_of_lt (Complex.abs_im_le_norm z) hz
    have hzero : ∀ k, iteratedDeriv k F 0 = 0 := by
      intro k
      rw [hder k, ← mom_ellpow, hN _ (Subalgebra.pow_mem _ (ell_mem ε b) k), mul_zero]
    have hloc : F =ᶠ[𝓝 0] 0 := by
      filter_upwards [Metric.ball_mem_nhds (0:ℂ) hδ] with z hz
      rw [← Complex.taylorSeries_eq_on_ball' hz (hd.mono hball)]
      simp [hzero]
    have han : AnalyticOnNhd ℂ F {z : ℂ | |z.im| < δ} := hd.analyticOnNhd (strip_open δ)
    have h0 : (0:ℂ) ∈ {z : ℂ | |z.im| < δ} := by simpa using hδ
    have h1 : (1:ℂ) ∈ {z : ℂ | |z.im| < δ} := by simpa using hδ
    have hF1 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (strip_conn δ) h0 hloc h1
    have e1 := hre 1 (by simp)
    rw [one_smul] at e1
    rw [← e1]
    exact hF1
  · intro hall R hR
    have hR' : R ∈ Submodule.span ℂ {R : PX m n | ∃ (b : Matrix (Fin n) (Fin n) ℂ) (k : ℕ),
        b.IsHermitian ∧ R = (∑ i : Fin n, ∑ j : Fin n, C (b i j) * Qp ε j i) ^ k} := by
      rw [← hP m n ε]
      exact hR
    clear hR
    induction hR' using Submodule.span_induction with
    | mem R hmem =>
      obtain ⟨b, k, hb, rfl⟩ := hmem
      obtain ⟨δ, hδ, hd, hre, hder⟩ := hS m n ε c t hc P b hb
      set F : ℂ → ℂ := fun z => ∫ x : Fin m → Fin n → ℂ,
        evX P x * gs c x * Complex.exp (Complex.I * ↑t * z * (b * gramX ε x).trace) with hF
      have han : AnalyticOnNhd ℂ F {z : ℂ | |z.im| < δ} := hd.analyticOnNhd (strip_open δ)
      have h0 : (0:ℂ) ∈ {z : ℂ | |z.im| < δ} := by simpa using hδ
      have hreal : ∀ r : ℝ, F r = 0 := by
        intro r
        rw [show F r = _ from hre (r:ℂ) (Complex.ofReal_im r)]
        apply hall
        unfold Matrix.IsHermitian
        rw [Matrix.conjTranspose_smul, hb.eq, Complex.star_def, Complex.conj_ofReal]
      have hfreq : ∃ᶠ z in 𝓝[≠] (0:ℂ), F z = 0 := by
        have hc0 : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝 0) (𝓝 0) := by
          simpa using Complex.continuous_ofReal.tendsto (0:ℝ)
        have hT : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
          refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            (hc0.mono_left nhdsWithin_le_nhds) ?_
          filter_upwards [self_mem_nhdsWithin] with r hr
          simpa using hr
        exact hT.frequently (Frequently.of_forall hreal)
      have hloc := ((han 0 h0).frequently_zero_iff_eventually_zero).mp hfreq
      have hk := hder k
      rw [Filter.EventuallyEq.iteratedDeriv_eq k (hloc : F =ᶠ[𝓝 0] 0)] at hk
      simp at hk
      rw [mom_ellpow]
      exact hk.resolve_left (fun h => ht h.1)
    | zero => exact mom_zero c P
    | add x y _ _ hx hy => rw [mom_add hc, hx, hy, add_zero]
    | smul a x _ hx => rw [mom_smul, hx, mul_zero]

end PositivityTheory.Rg.Sw.FFTSteps
