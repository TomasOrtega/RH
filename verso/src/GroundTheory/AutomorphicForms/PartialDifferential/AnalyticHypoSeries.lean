import Mathlib

namespace GroundTheory.Automorphic.Sobolev

open scoped ContDiff NNReal ENNReal Topology
open Set Filter

noncomputable section

section Converse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/- English proof (translation)
Establish `hz : HasDerivAt (fun τ : ℝ ↦ x₀ + τ • y) y t`. Simplify using `using ((hasDerivAt_id t).smul_const y).const_add x₀`. Establish `hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) (x₀ + t • y)` using `(hf.contDiffAt (hs.mem_nhds ht)).differentiableAt_iteratedFDeriv (by`. Conclude with `ENat.natCast_lt_top k)` after adjusting the coercions. Establish `h1` using `hd.hasFDerivAt.comp_hasDerivAt t hz`.

Establish `h2` using `(ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F (fun _ ↦ y)).hasFDerivAt.comp_hasDerivAt t h1`. Establish `e : iteratedFDeriv ℝ (k + 1) f (x₀ + t • y) (fun _ ↦ y) = (fderiv ℝ (iteratedFDeriv ℝ k f) (x₀ + t • y) y) (fun _ ↦ y)`. Rewrite using `[iteratedFDeriv_succ_apply_left]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `h2`.
-/
theorem hasDerivAt_iteratedFDeriv_line {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (x₀ y : E) (k : ℕ) {t : ℝ} (ht : x₀ + t • y ∈ s) :
    HasDerivAt (fun τ : ℝ ↦ iteratedFDeriv ℝ k f (x₀ + τ • y) (fun _ ↦ y))
      (iteratedFDeriv ℝ (k + 1) f (x₀ + t • y) (fun _ ↦ y)) t := by
  have hz : HasDerivAt (fun τ : ℝ ↦ x₀ + τ • y) y t := by
    simpa using ((hasDerivAt_id t).smul_const y).const_add x₀
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) (x₀ + t • y) :=
    (hf.contDiffAt (hs.mem_nhds ht)).differentiableAt_iteratedFDeriv (by
      exact_mod_cast ENat.natCast_lt_top k)
  have h1 := hd.hasFDerivAt.comp_hasDerivAt t hz
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F
    (fun _ ↦ y)).hasFDerivAt.comp_hasDerivAt t h1
  have e : iteratedFDeriv ℝ (k + 1) f (x₀ + t • y) (fun _ ↦ y) =
      (fderiv ℝ (iteratedFDeriv ℝ k f) (x₀ + t • y) y) (fun _ ↦ y) := by
    rw [iteratedFDeriv_succ_apply_left]; rfl
  rw [e]
  exact h2

/- English proof (translation)
Proceed by induction on `k generalizing t with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `hU : IsOpen {τ : ℝ | x₀ + τ • y ∈ s}` using `hs.preimage (by fun_prop)`. Establish `hev : iteratedDeriv k (fun τ : ℝ ↦ f (x₀ + τ • y)) =ᶠ[𝓝 t] fun τ ↦ iteratedFDeriv ℝ k f (x₀ + τ • y) (fun _ ↦ y)` using `by filter_upwards [hU.mem_nhds ht] with τ hτ using ih hτ`.

Rewrite using `[iteratedDeriv_succ, hev.deriv_eq]`. Conclude with `(hasDerivAt_iteratedFDeriv_line hs hf x₀ y k ht).deriv`.
-/
theorem iteratedDeriv_line_eq {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (x₀ y : E) (k : ℕ) {t : ℝ} (ht : x₀ + t • y ∈ s) :
    iteratedDeriv k (fun τ : ℝ ↦ f (x₀ + τ • y)) t =
      iteratedFDeriv ℝ k f (x₀ + t • y) (fun _ ↦ y) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    have hU : IsOpen {τ : ℝ | x₀ + τ • y ∈ s} := hs.preimage (by fun_prop)
    have hev : iteratedDeriv k (fun τ : ℝ ↦ f (x₀ + τ • y)) =ᶠ[𝓝 t]
        fun τ ↦ iteratedFDeriv ℝ k f (x₀ + τ • y) (fun _ ↦ y) := by
      filter_upwards [hU.mem_nhds ht] with τ hτ using ih hτ
    rw [iteratedDeriv_succ, hev.deriv_eq]
    exact (hasDerivAt_iteratedFDeriv_line hs hf x₀ y k ht).deriv

/- English proof (translation)
Use `set M' : ℝ := |M| + 1 with hM'`. Establish `hM'pos : 0 < M'` using `by positivity`. Establish `hb' : ∀ y ∈ Metric.ball x₀ r, ∀ k : ℕ, ‖iteratedFDeriv ℝ k f y‖ ≤ |C| * M' ^ k * k.factorial`. Introduce `y hy k`. Use `(hb y hy k).trans ?_` and prove the remaining obligations.

Establish `h1 : C * M ^ k ≤ |C| * M' ^ k`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `mul_le_mul_of_nonneg_right h1 (by positivity)`. Use `set ρ : ℝ := min r (1 / M') / 2 with hρ`.

Establish `hρpos : 0 < ρ` using `by positivity`. Establish `hρr : ρ < r`. Use `min_le_left r (1 / M')` as an intermediate fact. Rewrite using `[hρ]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hρM : M' * ρ ≤ 1 / 2`. Establish `h` using `min_le_right r (1 / M')`. Rewrite using `[hρ]`. Establish `: M' * (min r (1 / M')) ≤ 1`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set p : FormalMultilinearSeries ℝ E F := fun k ↦ ((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k f x₀ with hpdef`. Establish `hx₀ : x₀ ∈ Metric.ball x₀ r` using `Metric.mem_ball_self hr`. Establish `hp : ∀ k, ‖p k‖ ≤ |C| * M' ^ k`. Introduce `k`.

Establish `h` using `hb' x₀ hx₀ k`. Establish `hk : (0 : ℝ) < k.factorial` using `by exact_mod_cast Nat.factorial_pos k`. Simplify using `only [hpdef, norm_smul, norm_inv, Real.norm_natCast]`. Rewrite using `[inv_mul_le_iff₀ hk]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨p, ENNReal.ofReal ρ, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: ((Real.toNNReal ρ : ℝ≥0) : ℝ≥0∞) ≤ p.radius`. Use `p.le_radius_of_bound (|C|) fun k ↦ ?_` and prove the remaining obligations. Rewrite using `[Real.coe_toNNReal _ hρpos.le]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `pow_le_one₀ (by positivity) (by linarith)`. Use `_ = |C| := mul_one _`. Conclude with `this`. Simplify using `using hρpos`. Introduce `y hy`.

Establish `hy' : ‖y‖ < ρ`. Simplify `hy` using `[Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.ofReal, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hρpos.le]`. Use `set q : ℝ := M' * ‖y‖ with hq`. Establish `hq0 : 0 ≤ q` using `by positivity`. Establish `hq1 : q < 1`.

Establish `: M' * ‖y‖ < M' * ρ` using `mul_lt_mul_of_pos_left hy' hM'pos`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hterm : ∀ k, ‖p k (fun _ ↦ y)‖ ≤ |C| * q ^ k`. Introduce `k`. Combine the equalities or inequalities in the displayed calculation.

Establish `hsum : Summable fun k ↦ ‖p k (fun _ ↦ y)‖` using `Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm ((summable_geometric_of_lt_one hq0 hq1).mul_left _)`. Rewrite using `[hasSum_iff_tendsto_nat_of_summable_norm hsum]`. Rewrite using `[← Filter.tendsto_add_atTop_iff_nat 1]`. Use `set g : ℝ → F := fun τ ↦ f (x₀ + τ • y) with hg`. Establish `hline : ∀ τ ∈ Icc (0 : ℝ) 1, x₀ + τ • y ∈ Metric.ball x₀ r`.

Introduce `τ hτ`. Rewrite using `[Metric.mem_ball, dist_self_add_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]`. Combine the equalities or inequalities in the displayed calculation. Establish `hgAt : ∀ τ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ g τ`. Introduce `τ hτ`.

Establish `h1 : ContDiffAt ℝ ∞ f (x₀ + τ • y)` using `hf.contDiffAt (Metric.isOpen_ball.mem_nhds (hline τ hτ))`. Conclude with `h1.comp τ (by fun_prop)`. Establish `hder : ∀ k, ∀ τ ∈ Icc (0 : ℝ) 1, iteratedDerivWithin k g (Icc 0 1) τ = iteratedFDeriv ℝ k f (x₀ + τ • y) (fun _ ↦ y)`. Introduce `k τ hτ`. Rewrite using `[iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) ((hgAt τ hτ).of_le (by exact_mod_cast le_top)) hτ]`.

Conclude with `iteratedDeriv_line_eq Metric.isOpen_ball hf x₀ y k (hline τ hτ)`. Establish `hrem : ∀ N : ℕ, ‖(∑ k ∈ Finset.range (N + 1), p k (fun _ ↦ y)) - f (x₀ + y)‖ ≤ |C| * (((N + 1 : ℕ) : ℝ) * q ^ (N + 1))`. Introduce `N`. Establish `hgC : ContDiffOn ℝ (N + 1) g (Icc 0 1)` using `fun τ hτ ↦ ((hgAt τ hτ).of_le (by exact_mod_cast le_top)).contDiffWithinAt`. Establish `hbd : ∀ τ ∈ Icc (0 : ℝ) 1, ‖iteratedDerivWithin (N + 1) g (Icc 0 1) τ‖ ≤ |C| * M' ^ (N + 1) * ((N + 1).factorial : ℝ) * ‖y‖ ^ (N + 1)`.

Introduce `τ hτ`. Rewrite using `[hder (N + 1) τ hτ]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hb' _ (hline τ hτ) _`. Establish `hT` using `taylor_mean_remainder_bound (f := g) (n := N) zero_le_one hgC (right_mem_Icc.2 zero_le_one) hbd`.

Establish `hsumeq : taylorWithinEval g N (Icc 0 1) 0 1 = ∑ k ∈ Finset.range (N + 1), p k (fun _ ↦ y)`. Rewrite using `[taylor_within_apply]`. Use `Finset.sum_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[hder k 0 (left_mem_Icc.2 zero_le_one)]`. Simplify using `[hpdef]`.

Rewrite `hT` using `[hsumeq]`. Establish `hg1 : g 1 = f (x₀ + y)` using `by simp [hg]`. Rewrite `hT` using `[hg1, norm_sub_rev]`. Use `hT.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Nat.factorial_succ]`.

Establish `hN : (N.factorial : ℝ) ≠ 0` using `by positivity`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hq, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Establish `hlim : Tendsto (fun N : ℕ ↦ |C| * (((N + 1 : ℕ) : ℝ) * q ^ (N + 1))) atTop (𝓝 0)`. Establish `h` using `(tendsto_self_mul_const_pow_of_lt_one hq0 hq1).comp (tendsto_add_atTop_nat 1)`. Simplify using `using h.const_mul |C|`. Conclude with `squeeze_zero (fun _ ↦ norm_nonneg _) hrem hlim`.
-/
theorem analyticAt_of_norm_iteratedFDeriv_le {f : E → F} {x₀ : E} {r C M : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball x₀ r))
    (hb : ∀ y ∈ Metric.ball x₀ r, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ C * M ^ k * k.factorial) :
    AnalyticAt ℝ f x₀ := by
  set M' : ℝ := |M| + 1 with hM'
  have hM'pos : 0 < M' := by positivity
  have hb' : ∀ y ∈ Metric.ball x₀ r, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ |C| * M' ^ k * k.factorial := by
    intro y hy k
    refine (hb y hy k).trans ?_
    have h1 : C * M ^ k ≤ |C| * M' ^ k := by
      calc C * M ^ k ≤ |C * M ^ k| := le_abs_self _
        _ = |C| * |M| ^ k := by rw [abs_mul, abs_pow]
        _ ≤ |C| * M' ^ k := by
          gcongr
          linarith
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  set ρ : ℝ := min r (1 / M') / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hρr : ρ < r := by
    have := min_le_left r (1 / M')
    rw [hρ]; linarith
  have hρM : M' * ρ ≤ 1 / 2 := by
    have h := min_le_right r (1 / M')
    rw [hρ]
    have : M' * (min r (1 / M')) ≤ 1 := by
      calc M' * min r (1 / M') ≤ M' * (1 / M') := by gcongr
        _ = 1 := by field_simp
    linarith
  set p : FormalMultilinearSeries ℝ E F :=
    fun k ↦ ((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k f x₀ with hpdef
  have hx₀ : x₀ ∈ Metric.ball x₀ r := Metric.mem_ball_self hr
  have hp : ∀ k, ‖p k‖ ≤ |C| * M' ^ k := by
    intro k
    have h := hb' x₀ hx₀ k
    have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    simp only [hpdef, norm_smul, norm_inv, Real.norm_natCast]
    rw [inv_mul_le_iff₀ hk]
    linarith
  refine ⟨p, ENNReal.ofReal ρ, ?_, ?_, ?_⟩
  · have : ((Real.toNNReal ρ : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
      refine p.le_radius_of_bound (|C|) fun k ↦ ?_
      rw [Real.coe_toNNReal _ hρpos.le]
      calc ‖p k‖ * ρ ^ k ≤ |C| * M' ^ k * ρ ^ k := by gcongr; exact hp k
        _ = |C| * (M' * ρ) ^ k := by ring
        _ ≤ |C| * 1 := by
          gcongr
          exact pow_le_one₀ (by positivity) (by linarith)
        _ = |C| := mul_one _
    exact this
  · simpa using hρpos
  · intro y hy
    have hy' : ‖y‖ < ρ := by
      simpa [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.ofReal,
        ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hρpos.le] using hy

    set q : ℝ := M' * ‖y‖ with hq
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q < 1 := by
      have : M' * ‖y‖ < M' * ρ := mul_lt_mul_of_pos_left hy' hM'pos
      linarith
    have hterm : ∀ k, ‖p k (fun _ ↦ y)‖ ≤ |C| * q ^ k := by
      intro k
      calc ‖p k (fun _ ↦ y)‖ ≤ ‖p k‖ * ∏ _i : Fin k, ‖y‖ := (p k).le_opNorm _
        _ = ‖p k‖ * ‖y‖ ^ k := by simp
        _ ≤ |C| * M' ^ k * ‖y‖ ^ k := by gcongr; exact hp k
        _ = |C| * q ^ k := by rw [hq, mul_pow]; ring
    have hsum : Summable fun k ↦ ‖p k (fun _ ↦ y)‖ :=
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm
        ((summable_geometric_of_lt_one hq0 hq1).mul_left _)
    rw [hasSum_iff_tendsto_nat_of_summable_norm hsum]
    rw [← Filter.tendsto_add_atTop_iff_nat 1]

    set g : ℝ → F := fun τ ↦ f (x₀ + τ • y) with hg
    have hline : ∀ τ ∈ Icc (0 : ℝ) 1, x₀ + τ • y ∈ Metric.ball x₀ r := by
      intro τ hτ
      rw [Metric.mem_ball, dist_self_add_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hτ.1]
      calc τ * ‖y‖ ≤ 1 * ‖y‖ := by gcongr; exact hτ.2
        _ < r := by linarith
    have hgAt : ∀ τ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ g τ := by
      intro τ hτ
      have h1 : ContDiffAt ℝ ∞ f (x₀ + τ • y) :=
        hf.contDiffAt (Metric.isOpen_ball.mem_nhds (hline τ hτ))
      exact h1.comp τ (by fun_prop)
    have hder : ∀ k, ∀ τ ∈ Icc (0 : ℝ) 1, iteratedDerivWithin k g (Icc 0 1) τ =
        iteratedFDeriv ℝ k f (x₀ + τ • y) (fun _ ↦ y) := by
      intro k τ hτ
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
        ((hgAt τ hτ).of_le (by exact_mod_cast le_top)) hτ]
      exact iteratedDeriv_line_eq Metric.isOpen_ball hf x₀ y k (hline τ hτ)
    have hrem : ∀ N : ℕ, ‖(∑ k ∈ Finset.range (N + 1), p k (fun _ ↦ y)) - f (x₀ + y)‖ ≤
        |C| * (((N + 1 : ℕ) : ℝ) * q ^ (N + 1)) := by
      intro N
      have hgC : ContDiffOn ℝ (N + 1) g (Icc 0 1) := fun τ hτ ↦
        ((hgAt τ hτ).of_le (by exact_mod_cast le_top)).contDiffWithinAt
      have hbd : ∀ τ ∈ Icc (0 : ℝ) 1, ‖iteratedDerivWithin (N + 1) g (Icc 0 1) τ‖ ≤
          |C| * M' ^ (N + 1) * ((N + 1).factorial : ℝ) * ‖y‖ ^ (N + 1) := by
        intro τ hτ
        rw [hder (N + 1) τ hτ]
        calc ‖iteratedFDeriv ℝ (N + 1) f (x₀ + τ • y) (fun _ ↦ y)‖
            ≤ ‖iteratedFDeriv ℝ (N + 1) f (x₀ + τ • y)‖ * ∏ _i : Fin (N + 1), ‖y‖ :=
              ContinuousMultilinearMap.le_opNorm _ _
          _ = ‖iteratedFDeriv ℝ (N + 1) f (x₀ + τ • y)‖ * ‖y‖ ^ (N + 1) := by simp
          _ ≤ |C| * M' ^ (N + 1) * ((N + 1).factorial : ℝ) * ‖y‖ ^ (N + 1) := by
              gcongr
              exact hb' _ (hline τ hτ) _
      have hT := taylor_mean_remainder_bound (f := g) (n := N) zero_le_one hgC
        (right_mem_Icc.2 zero_le_one) hbd
      have hsumeq : taylorWithinEval g N (Icc 0 1) 0 1 =
          ∑ k ∈ Finset.range (N + 1), p k (fun _ ↦ y) := by
        rw [taylor_within_apply]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [hder k 0 (left_mem_Icc.2 zero_le_one)]
        simp [hpdef]
      rw [hsumeq] at hT
      have hg1 : g 1 = f (x₀ + y) := by simp [hg]
      rw [hg1, norm_sub_rev] at hT
      refine hT.trans (le_of_eq ?_)
      rw [Nat.factorial_succ]
      have hN : (N.factorial : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      rw [hq, mul_pow]
      ring
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun N : ℕ ↦ |C| * (((N + 1 : ℕ) : ℝ) * q ^ (N + 1))) atTop (𝓝 0) := by
      have h := (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).comp (tendsto_add_atTop_nat 1)
      simpa using h.const_mul |C|
    exact squeeze_zero (fun _ ↦ norm_nonneg _) hrem hlim

end Converse

section Forward

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

/- English proof (translation)
Use `ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v ↦ ?_` and prove the remaining obligations. Rewrite using `[h.iteratedFDeriv_eq_sum_of_completeSpace v]`. Combine the equalities or inequalities in the displayed calculation. Use `((q k).le_opNorm _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`.

Conclude with `Equiv.prod_comp σ (fun i ↦ ‖v i‖)`. Use `_ = k.factorial * ‖q k‖ * ∏ i, ‖v i‖ := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall {f : E → F}
    {q : FormalMultilinearSeries ℝ E F} {y : E} {R : ℝ≥0∞} (h : HasFPowerSeriesOnBall f q y R)
    (k : ℕ) : ‖iteratedFDeriv ℝ k f y‖ ≤ k.factorial * ‖q k‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v ↦ ?_
  rw [h.iteratedFDeriv_eq_sum_of_completeSpace v]
  calc ‖∑ σ : Equiv.Perm (Fin k), q k (fun i ↦ v (σ i))‖
      ≤ ∑ σ : Equiv.Perm (Fin k), ‖q k (fun i ↦ v (σ i))‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin k), ‖q k‖ * ∏ i, ‖v i‖ := by
        gcongr with σ
        refine ((q k).le_opNorm _).trans (le_of_eq ?_)
        congr 1
        exact Equiv.prod_comp σ (fun i ↦ ‖v i‖)
    _ = k.factorial * ‖q k‖ * ∏ i, ‖v i‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]
        ring

/- English proof (translation)
Establish `hsum` using `p.changeOriginSeries_summable_aux₂ hzr k`. Establish `h1` using `p.nnnorm_changeOrigin_le k hzr`. Rewrite `h1`, the goal using `[← ENNReal.coe_le_coe]`. Use `h1.trans ?_` and prove the remaining obligations. Rewrite using `[ENNReal.coe_tsum hsum, ENNReal.tsum_sigma']`.

Establish `hterm : ∀ l : ℕ, ∑' _b : { s : Finset (Fin (k + l)) // s.card = l }, ((‖p (k + l)‖₊ * ‖z‖₊ ^ l : ℝ≥0) : ℝ≥0∞) ≤ ((K * (2 / ρ) ^ k * (2⁻¹) ^ l : ℝ≥0) : ℝ≥0∞)`. Introduce `l`. Rewrite using `[tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin, nsmul_eq_mul, ← ENNReal.coe_natCast, ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]`. Establish `hK'` using `hK (k + l)`. Rewrite `hK'` using `[← NNReal.coe_le_coe]`.

Move the coercions through the operations in `at hK' ⊢`. Establish `hz' : 4 * ‖z‖ ≤ (ρ : ℝ)` using `by exact_mod_cast hz`. Establish `hch : ((k + l).choose l : ℝ) ≤ 2 ^ (k + l)`. Conclude with `Nat.choose_le_two_pow _ _` after adjusting the coercions. Establish `hρ' : (0 : ℝ) < ρ` using `hρ`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = (K : ℝ) * (2 / (ρ : ℝ)) ^ k * (2⁻¹) ^ l := by`. Establish `h4 : (4 : ℝ) ^ l = 2 ^ l * 2 ^ l` using `by rw [← mul_pow]; norm_num`. Rewrite using `[pow_add, pow_add, div_pow, div_pow, inv_pow, h4]`.

Clear the denominators using the available nonvanishing facts. Use `(ENNReal.tsum_le_tsum hterm).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_inv_two]`. Rewrite using `[ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem nnnorm_changeOrigin_le_of_bound (p : FormalMultilinearSeries ℝ E F) {ρ K : ℝ≥0}
    (hρ : 0 < ρ) (hK : ∀ n, ‖p n‖₊ ≤ K / ρ ^ n) {z : E} (hz : 4 * ‖z‖₊ ≤ ρ)
    (hzr : (‖z‖₊ : ℝ≥0∞) < p.radius) (k : ℕ) :
    ‖p.changeOrigin z k‖₊ ≤ 2 * (K * (2 / ρ) ^ k) := by
  have hsum := p.changeOriginSeries_summable_aux₂ hzr k
  have h1 := p.nnnorm_changeOrigin_le k hzr
  rw [← ENNReal.coe_le_coe] at h1 ⊢
  refine h1.trans ?_
  rw [ENNReal.coe_tsum hsum, ENNReal.tsum_sigma']
  have hterm : ∀ l : ℕ, ∑' _b : { s : Finset (Fin (k + l)) // s.card = l },
      ((‖p (k + l)‖₊ * ‖z‖₊ ^ l : ℝ≥0) : ℝ≥0∞)
      ≤ ((K * (2 / ρ) ^ k * (2⁻¹) ^ l : ℝ≥0) : ℝ≥0∞) := by
    intro l
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_finset_len,
      Fintype.card_fin, nsmul_eq_mul, ← ENNReal.coe_natCast, ← ENNReal.coe_mul,
      ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    have hK' := hK (k + l)
    rw [← NNReal.coe_le_coe] at hK'
    push_cast at hK' ⊢
    have hz' : 4 * ‖z‖ ≤ (ρ : ℝ) := by exact_mod_cast hz
    have hch : ((k + l).choose l : ℝ) ≤ 2 ^ (k + l) := by
      exact_mod_cast Nat.choose_le_two_pow _ _
    have hρ' : (0 : ℝ) < ρ := hρ
    calc ((k + l).choose l : ℝ) * (‖p (k + l)‖ * ‖z‖ ^ l)
        ≤ 2 ^ (k + l) * ((K : ℝ) / (ρ : ℝ) ^ (k + l) * ((ρ : ℝ) / 4) ^ l) := by
          gcongr
          linarith
      _ = (K : ℝ) * (2 / (ρ : ℝ)) ^ k * (2⁻¹) ^ l := by
          have h4 : (4 : ℝ) ^ l = 2 ^ l * 2 ^ l := by rw [← mul_pow]; norm_num
          rw [pow_add, pow_add, div_pow, div_pow, inv_pow, h4]
          field_simp
  refine (ENNReal.tsum_le_tsum hterm).trans (le_of_eq ?_)
  simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_inv_two]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  push_cast
  ring

/- English proof (translation)
Take `⟨p, R, hp⟩` from `hf`. Take `⟨ρ, hρ0', hρR⟩` from `ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos`. Establish `hρ0 : 0 < ρ` using `ENNReal.coe_pos.1 hρ0'`. Take `⟨K, hK0, hK⟩` from `p.norm_le_div_pow_of_pos_of_lt_radius hρ0 (hρR.trans_le hp.r_le)`. Use `set K' : ℝ≥0 := ⟨K, hK0.le⟩ with hK'def`.

Establish `hK' : ∀ n, ‖p n‖₊ ≤ K' / ρ ^ n` using `fun n ↦ by`. Rewrite using `[← NNReal.coe_le_coe]`. Use `push_cast`. Conclude with `hK n`. Establish `hρ' : (0 : ℝ) < ρ` using `hρ0`.

Use `⟨(ρ : ℝ) / 4, by positivity, 2 * K, 2 / ρ, by positivity, by positivity, fun y hy k ↦ ?_⟩` and prove the remaining obligations. Use `set z := y - x₀ with hzdef`. Establish `hz : ‖z‖ < (ρ : ℝ) / 4` using `by rwa [Metric.mem_ball, dist_eq_norm] at hy`. Establish `hzρ : ‖z‖₊ < ρ`. Rewrite using `[← NNReal.coe_lt_coe, coe_nnnorm]`.

Combine the linear relations using `[norm_nonneg z]`. Establish `hzR : (‖z‖₊ : ℝ≥0∞) < R` using `lt_trans (by exact_mod_cast hzρ) hρR`. Establish `hq` using `hp.changeOrigin hzR`. Establish `hxy : x₀ + z = y` using `by simp [hzdef]`. Rewrite `hq` using `[hxy]`.

Use `(norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall hq k).trans ?_` and prove the remaining obligations. Establish `hb` using `nnnorm_changeOrigin_le_of_bound p hρ0 hK' (z := z) (by rw [← NNReal.coe_le_coe]; push_cast; linarith) (hzR.trans_le hp.r_le) k`. Rewrite `hb` using `[← NNReal.coe_le_coe]`. Move the coercions through the operations in `at hb`. Establish `hb' : ‖p.changeOrigin z k‖ ≤ 2 * (K * (2 / ρ) ^ k)` using `hb`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_norm_iteratedFDeriv_le_of_analyticAt {f : E → F} {x₀ : E}
    (hf : AnalyticAt ℝ f x₀) :
    ∃ r > 0, ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ y ∈ Metric.ball x₀ r, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ C * M ^ k * k.factorial := by
  obtain ⟨p, R, hp⟩ := hf
  obtain ⟨ρ, hρ0', hρR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  have hρ0 : 0 < ρ := ENNReal.coe_pos.1 hρ0'
  obtain ⟨K, hK0, hK⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hρ0 (hρR.trans_le hp.r_le)
  set K' : ℝ≥0 := ⟨K, hK0.le⟩ with hK'def
  have hK' : ∀ n, ‖p n‖₊ ≤ K' / ρ ^ n := fun n ↦ by
    rw [← NNReal.coe_le_coe]; push_cast; exact hK n
  have hρ' : (0 : ℝ) < ρ := hρ0
  refine ⟨(ρ : ℝ) / 4, by positivity, 2 * K, 2 / ρ, by positivity, by positivity,
    fun y hy k ↦ ?_⟩
  set z := y - x₀ with hzdef
  have hz : ‖z‖ < (ρ : ℝ) / 4 := by rwa [Metric.mem_ball, dist_eq_norm] at hy
  have hzρ : ‖z‖₊ < ρ := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm]; linarith [norm_nonneg z]
  have hzR : (‖z‖₊ : ℝ≥0∞) < R := lt_trans (by exact_mod_cast hzρ) hρR
  have hq := hp.changeOrigin hzR
  have hxy : x₀ + z = y := by simp [hzdef]
  rw [hxy] at hq
  refine (norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall hq k).trans ?_
  have hb := nnnorm_changeOrigin_le_of_bound p hρ0 hK'
    (z := z) (by rw [← NNReal.coe_le_coe]; push_cast; linarith) (hzR.trans_le hp.r_le) k
  rw [← NNReal.coe_le_coe] at hb
  push_cast at hb
  have hb' : ‖p.changeOrigin z k‖ ≤ 2 * (K * (2 / ρ) ^ k) := hb
  calc (k.factorial : ℝ) * ‖p.changeOrigin z k‖ ≤ k.factorial * (2 * (K * (2 / ρ) ^ k)) := by
        gcongr
    _ = 2 * K * (2 / ρ) ^ k * k.factorial := by ring

end Forward

end

end GroundTheory.Automorphic.Sobolev
