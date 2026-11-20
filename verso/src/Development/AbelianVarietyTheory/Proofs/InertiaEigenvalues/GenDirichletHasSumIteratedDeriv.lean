import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandauSummableOfExpDirichletSeriesEntire
open MeasureTheory Complex Classical Filter Topology

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[norm_mul, Complex.norm_real, Complex.norm_exp, Real.norm_of_nonneg ha]`. Use `congr 2`. Simplify using the standard rewrite rules.
-/
theorem genDirichlet_term_norm (a l : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    ‖(a : ℂ) * Complex.exp (-(l : ℂ) * z)‖ = a * Real.exp (-l * z.re) := by
  rw [norm_mul, Complex.norm_real, Complex.norm_exp, Real.norm_of_nonneg ha]
  congr 2
  simp

/- English proof (translation)
Use `Summable.of_norm_bounded hy (fun i => ?_)` and prove the remaining obligations. Rewrite using `[genDirichlet_term_norm _ _ (ha i)]`. Conclude with `mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (ha i)`.
-/
theorem genDirichlet_summable_of_le {ι : Type} (a l : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hl : ∀ i, 0 ≤ l i) {y : ℝ} (hy : Summable (fun i => a i * Real.exp (-(l i) * y)))
    {z : ℂ} (hz : y ≤ z.re) :
    Summable (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * z)) := by
  refine Summable.of_norm_bounded hy (fun i => ?_)
  rw [genDirichlet_term_norm _ _ (ha i)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (ha i)

/- English proof (translation)
Introduce `z hz`. Establish `hz' : s < z.re` using `hz`. Establish `hU : IsOpen {w : ℂ | (s + z.re) / 2 < w.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `hD : DifferentiableOn ℂ (fun z : ℂ => ∑' i, (a i : ℂ) * Complex.exp (-(l i : ℂ) * z)) {w : ℂ | (s + z.re) / 2 < w.re}` using `Complex.differentiableOn_tsum_of_summable_norm (hs ((s + z.re) / 2) (by linarith)) (fun i => by fun_prop) hU (fun i w hw => by`. Establish `hw' : (s + z.re) / 2 < w.re` using `hw`.

Rewrite using `[genDirichlet_term_norm _ _ (ha i)]`. Conclude with `mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (ha i))`. Conclude with `(hD.differentiableAt (hU.mem_nhds (show (s + z.re) / 2 < z.re by linarith))).differentiableWithinAt`.
-/
theorem genDirichlet_differentiableOn {ι : Type} (a l : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hl : ∀ i, 0 ≤ l i) (s : ℝ)
    (hs : ∀ y : ℝ, s < y → Summable (fun i => a i * Real.exp (-(l i) * y))) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' i, (a i : ℂ) * Complex.exp (-(l i : ℂ) * z))
      {z : ℂ | s < z.re} := by
  intro z hz
  have hz' : s < z.re := hz
  have hU : IsOpen {w : ℂ | (s + z.re) / 2 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hD : DifferentiableOn ℂ (fun z : ℂ => ∑' i, (a i : ℂ) * Complex.exp (-(l i : ℂ) * z))
      {w : ℂ | (s + z.re) / 2 < w.re} :=
    Complex.differentiableOn_tsum_of_summable_norm (hs ((s + z.re) / 2) (by linarith)) (fun i => by fun_prop) hU
      (fun i w hw => by
        have hw' : (s + z.re) / 2 < w.re := hw
        rw [genDirichlet_term_norm _ _ (ha i)]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (ha i))
  exact (hD.differentiableAt (hU.mem_nhds (show (s + z.re) / 2 < z.re by linarith))).differentiableWithinAt

/- English proof (translation)
Use `set δ := (σ - t) / 2 with hδ`. Establish `hδ0 : 0 < δ` using `by rw [hδ]; linarith`. Establish `h1` using `(h (σ - δ) (by rw [hδ]; linarith)).mul_left ((n.factorial : ℝ) / δ ^ n)`. Use `Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) h1` and prove the remaining obligations. Use `hb j` as an intermediate fact.

Use `hμ j` as an intermediate fact. Check the signs of the components of the expression. Establish `h2` using `Real.pow_div_factorial_le_exp (μ j * δ) (mul_nonneg (hμ j) hδ0.le) n`. Establish `hf : (0:ℝ) < n.factorial` using `by positivity`. Establish `h3 : μ j ^ n ≤ (n.factorial : ℝ) / δ ^ n * Real.exp (μ j * δ)`.

Rewrite `h2` using `[div_le_iff₀ hf, mul_pow]`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : Real.exp (-(μ j) * (σ - δ)) = Real.exp (μ j * δ) * Real.exp (-(μ j) * σ)`. Rewrite using `[← Real.exp_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4]`. Establish `h5 : 0 ≤ b j * Real.exp (-(μ j) * σ)` using `mul_nonneg (hb j) (Real.exp_pos _).le`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem genDirichlet_summable_pow {ι : Type} (b μ : ι → ℝ) (hb : ∀ j, 0 ≤ b j) (hμ : ∀ j, 0 ≤ μ j)
    (t : ℝ) (h : ∀ σ : ℝ, t < σ → Summable (fun j => b j * Real.exp (-(μ j) * σ))) (n : ℕ) (σ : ℝ)
    (hσ : t < σ) :
    Summable (fun j => b j * μ j ^ n * Real.exp (-(μ j) * σ)) := by
  set δ := (σ - t) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have h1 := (h (σ - δ) (by rw [hδ]; linarith)).mul_left ((n.factorial : ℝ) / δ ^ n)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) h1
  · have := hb j; have := hμ j; positivity
  · have h2 := Real.pow_div_factorial_le_exp (μ j * δ) (mul_nonneg (hμ j) hδ0.le) n
    have hf : (0:ℝ) < n.factorial := by positivity
    have h3 : μ j ^ n ≤ (n.factorial : ℝ) / δ ^ n * Real.exp (μ j * δ) := by
      rw [div_le_iff₀ hf, mul_pow] at h2
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    have h4 : Real.exp (-(μ j) * (σ - δ)) = Real.exp (μ j * δ) * Real.exp (-(μ j) * σ) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h4]
    have h5 : 0 ≤ b j * Real.exp (-(μ j) * σ) := mul_nonneg (hb j) (Real.exp_pos _).le
    calc b j * μ j ^ n * Real.exp (-(μ j) * σ) = μ j ^ n * (b j * Real.exp (-(μ j) * σ)) := by ring
      _ ≤ ((n.factorial : ℝ) / δ ^ n * Real.exp (μ j * δ)) * (b j * Real.exp (-(μ j) * σ)) :=
        mul_le_mul_of_nonneg_right h3 h5
      _ = _ := by ring

/- English proof (translation)
Establish `hreal : ∀ σ : ℝ, t < σ → Summable (fun j => b j * Real.exp (-(μ j) * σ))`. Introduce `σ hσ`. Use `(h σ (by simpa using hσ)).summable` as an intermediate fact. Rewrite using `[← Complex.summable_ofReal]`. Use `this using 2` and compare the differences between its conclusion and the goal.

Use `push_cast`. Both sides reduce to the same expression. Proceed by induction on `n generalizing s with`. Consider the case `zero => simpa using h s hs`. Consider the case `succ n ih => set σ := (t + s.re) / 2 with hσ`.

Establish `hσ1 : t < σ` using `by rw [hσ]; linarith`. Establish `hσs : σ < s.re` using `by rw [hσ]; linarith`. Establish `hU : IsOpen {w : ℂ | σ < w.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `key` using `Complex.hasSum_deriv_of_summable_norm (F := fun j w => (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * w)) (U := {w : ℂ | σ < w.re}) (z := s) (genDirichlet_summable_pow b μ hb hμ t hreal n σ hσ1) (fun j => by fun_prop) hU (fun j w hw => by`. Establish `hw' : σ < w.re` using `hw`.

Rewrite using `[norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Complex.norm_real, Complex.norm_exp, Real.norm_of_nonneg (hb j), Real.norm_of_nonneg (hμ j)]`. Establish `h0 : 0 ≤ b j * μ j ^ n` using `mul_nonneg (hb j) (pow_nonneg (hμ j) n)`. Use `mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) h0` and prove the remaining obligations. Use `hμ j` as an intermediate fact. Simplify using the standard rewrite rules.

Use the proof step `nlinarith) hσs`. Establish `hev : (fun w : ℂ => ∑' j, (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * w)) =ᶠ[nhds s] iteratedDeriv n F` using `by filter_upwards [hU.mem_nhds hσs] with w hw`. Establish `hw' : σ < w.re` using `hw`. Conclude with `(ih w (by linarith)).tsum_eq`. Rewrite `key` using `[hev.deriv_eq, ← iteratedDeriv_succ]`.

Use `(congrArg (fun f => HasSum f _) (funext fun j => ?_)).mp key` and prove the remaining obligations. Establish `: HasDerivAt (fun w : ℂ => (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * w)) ((b j : ℂ) * (-(μ j : ℂ)) ^ n * (Complex.exp (-(μ j : ℂ) * s) * (-(μ j : ℂ) * 1))) s` using `(((hasDerivAt_id s).const_mul (-(μ j : ℂ))).cexp).const_mul _`. Rewrite using `[this.deriv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem genDirichlet_hasSum_iteratedDeriv {ι : Type} (b μ : ι → ℝ) (F : ℂ → ℂ)
    (hb : ∀ j, 0 ≤ b j) (hμ : ∀ j, 0 ≤ μ j) (t : ℝ)
    (h : ∀ s : ℂ, t < s.re → HasSum (fun j => (b j : ℂ) * Complex.exp (-(μ j : ℂ) * s)) (F s))
    (n : ℕ) (s : ℂ) (hs : t < s.re) :
    HasSum (fun j => (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * s))
      (iteratedDeriv n F s) := by
  have hreal : ∀ σ : ℝ, t < σ → Summable (fun j => b j * Real.exp (-(μ j) * σ)) := by
    intro σ hσ
    have := (h σ (by simpa using hσ)).summable
    rw [← Complex.summable_ofReal]
    convert this using 2
    push_cast; rfl
  induction n generalizing s with
  | zero => simpa using h s hs
  | succ n ih =>
    set σ := (t + s.re) / 2 with hσ
    have hσ1 : t < σ := by rw [hσ]; linarith
    have hσs : σ < s.re := by rw [hσ]; linarith
    have hU : IsOpen {w : ℂ | σ < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have key := Complex.hasSum_deriv_of_summable_norm
      (F := fun j w => (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * w))
      (U := {w : ℂ | σ < w.re}) (z := s)
      (genDirichlet_summable_pow b μ hb hμ t hreal n σ hσ1)
      (fun j => by fun_prop) hU (fun j w hw => by
        have hw' : σ < w.re := hw
        rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Complex.norm_real,
          Complex.norm_exp, Real.norm_of_nonneg (hb j), Real.norm_of_nonneg (hμ j)]
        have h0 : 0 ≤ b j * μ j ^ n := mul_nonneg (hb j) (pow_nonneg (hμ j) n)
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) h0
        have := hμ j
        simp
        nlinarith) hσs
    have hev : (fun w : ℂ => ∑' j, (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * w))
        =ᶠ[nhds s] iteratedDeriv n F := by
      filter_upwards [hU.mem_nhds hσs] with w hw
      have hw' : σ < w.re := hw
      exact (ih w (by linarith)).tsum_eq
    rw [hev.deriv_eq, ← iteratedDeriv_succ] at key
    refine (congrArg (fun f => HasSum f _) (funext fun j => ?_)).mp key
    have : HasDerivAt (fun w : ℂ => (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * w))
        ((b j : ℂ) * (-(μ j : ℂ)) ^ n * (Complex.exp (-(μ j : ℂ) * s) * (-(μ j : ℂ) * 1))) s :=
      (((hasDerivAt_id s).const_mul (-(μ j : ℂ))).cexp).const_mul _
    rw [this.deriv]; ring

/- English proof (translation)
Establish `hU : IsOpen (Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re})` using `Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)`. Establish `hconv : Convex ℝ (Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re})` using `(convex_ball _ _).inter (convex_halfSpace_re_gt s)`. Establish `hFa : AnalyticOnNhd ℂ F (Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re})` using `(hF.mono Set.inter_subset_left).analyticOnNhd hU`. Establish `hΦa : AnalyticOnNhd ℂ Φ (Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re})` using `(hΦ.mono Set.inter_subset_right).analyticOnNhd hU`. Establish `hc : ((T + r / 2 : ℝ) : ℂ) ∈ Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re}`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]`. Apply the tactic sequence `constructor <;> linarith`. Use `show s < ((T + r / 2 : ℝ) : ℂ).re`. Rewrite using `[Complex.ofReal_re]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfreq : ∃ᶠ z in 𝓝[≠] ((T + r / 2 : ℝ) : ℂ), F z = Φ z`. Establish `ht : Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[>] (T + r / 2)) (𝓝[≠] ((T + r / 2 : ℝ) : ℂ))`. Use `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_` and prove the remaining obligations. Conclude with `(Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds`.

Use `filter_upwards [self_mem_nhdsWithin] with y hy`. Simplify using `only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_inj]`. Conclude with `ne_of_gt hy`. Use `ht.frequently (Eventually.frequently ?_)` and prove the remaining obligations. Establish `: Set.Ioo (T + r / 2) (T + r) ∈ 𝓝[>] (T + r / 2)` using `Ioo_mem_nhdsGT (by linarith)`.

Use `filter_upwards [this] with y hy`. Conclude with `heq y (by linarith [hy.1]) hy.2`. Conclude with `hFa.eqOn_of_preconnected_of_frequently_eq hΦa hconv.isPreconnected hc hfreq`.
-/
theorem genDirichlet_eqOn_ball_inter {F Φ : ℂ → ℂ} {T r s : ℝ} (hr : 0 < r) (hsT : s ≤ T)
    (hF : DifferentiableOn ℂ F (Metric.ball (T : ℂ) r))
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | s < z.re})
    (heq : ∀ y : ℝ, T < y → y < T + r → F y = Φ y) :
    ∀ z ∈ Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re}, F z = Φ z := by
  have hU : IsOpen (Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re}) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hconv : Convex ℝ (Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re}) :=
    (convex_ball _ _).inter (convex_halfSpace_re_gt s)
  have hFa : AnalyticOnNhd ℂ F (Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re}) :=
    (hF.mono Set.inter_subset_left).analyticOnNhd hU
  have hΦa : AnalyticOnNhd ℂ Φ (Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re}) :=
    (hΦ.mono Set.inter_subset_right).analyticOnNhd hU
  have hc : ((T + r / 2 : ℝ) : ℂ) ∈ Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re} := by
    constructor
    · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    · show s < ((T + r / 2 : ℝ) : ℂ).re
      rw [Complex.ofReal_re]; linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] ((T + r / 2 : ℝ) : ℂ), F z = Φ z := by
    have ht : Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[>] (T + r / 2)) (𝓝[≠] ((T + r / 2 : ℝ) : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_inj]
        exact ne_of_gt hy
    refine ht.frequently (Eventually.frequently ?_)
    have : Set.Ioo (T + r / 2) (T + r) ∈ 𝓝[>] (T + r / 2) := Ioo_mem_nhdsGT (by linarith)
    filter_upwards [this] with y hy
    exact heq y (by linarith [hy.1]) hy.2
  exact hFa.eqOn_of_preconnected_of_frequently_eq hΦa hconv.isPreconnected hc hfreq

/- English proof (translation)
Take `⟨r, hr, hFr⟩` from `hFa.exists_ball_analyticOnNhd`. Establish `hFd : DifferentiableOn ℂ F (Metric.ball (T : ℂ) r)` using `hFr.differentiableOn`. Establish `hrealT : ∀ y : ℝ, T < y → Summable (fun i => a i * Real.exp (-(l i) * y))`. Introduce `y hy`. Use `(hP y hy).summable` as an intermediate fact.

Rewrite using `[← Complex.summable_ofReal]`. Use `this using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Both sides reduce to the same expression. Take `⟨δ, hδ0, hδr, hδT⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ r / 4 ∧ δ ≤ (T - x₀) / 2` from `⟨min (r / 4) ((T - x₀) / 2), lt_min (by linarith) (by linarith), min_le_left _ _, min_le_right _ _⟩`.

Establish `hΦT` using `genDirichlet_differentiableOn a l ha hl T hrealT`. Establish `hEq1` using `genDirichlet_eqOn_ball_inter hr le_rfl hFd hΦT (fun y hy _ => ((hP y hy).tsum_eq).symm)`. Establish `hU : IsOpen (Metric.ball (T : ℂ) r ∩ {z : ℂ | T < z.re})` using `Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)`. Establish `hcm : ((T + δ : ℝ) : ℂ) ∈ Metric.ball (T : ℂ) r ∩ {z : ℂ | T < z.re}`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]`. Apply the tactic sequence `constructor <;> linarith`. Use `show T < ((T + δ : ℝ) : ℂ).re`. Rewrite using `[Complex.ofReal_re]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hev : F =ᶠ[𝓝 ((T + δ : ℝ) : ℂ)] (fun z : ℂ => ∑' i, (a i : ℂ) * Complex.exp (-(l i : ℂ) * z))` using `by filter_upwards [hU.mem_nhds hcm] with z hz using hEq1 z hz`. Establish `hΦsum : ∀ s : ℂ, T < s.re → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * s)) ((fun z : ℂ => ∑' i, (a i : ℂ) * Complex.exp (-(l i : ℂ) * z)) s)` using `fun s hs => (genDirichlet_summable_of_le a l ha hl (hrealT s.re hs) le_rfl).hasSum`. Establish `hder : ∀ n : ℕ, HasSum (fun i => (a i : ℂ) * (-(l i : ℂ)) ^ n * Complex.exp (-(l i : ℂ) * ((T + δ : ℝ) : ℂ))) (iteratedDeriv n F ((T + δ : ℝ) : ℂ))`. Introduce `n`. Rewrite using `[hev.iteratedDeriv_eq n]`.

Conclude with `genDirichlet_hasSum_iteratedDeriv a l _ ha hl T hΦsum n _ (by rw [Complex.ofReal_re]; linarith)`. Establish `hball : Metric.ball ((T + δ : ℝ) : ℂ) (r - δ) ⊆ Metric.ball (T : ℂ) r`. Introduce `z hz`. Rewrite `hz`, the goal using `[Metric.mem_ball]`. Establish `hd : dist ((T + δ : ℝ) : ℂ) (T : ℂ) = δ`.

Rewrite using `[Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hδ0]`. Combine the equalities or inequalities in the displayed calculation. Establish `hz : ((T - δ : ℝ) : ℂ) ∈ Metric.ball ((T + δ : ℝ) : ℂ) (r - δ)`. Rewrite using `[Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, show T - δ - (T + δ) = -(2 * δ) by ring, abs_neg, abs_of_pos (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hTay` using `Complex.hasSum_re (Complex.hasSum_taylorSeries_on_ball (hFd.mono hball) hz)`. Establish `hj : ∀ j, HasSum (fun n : ℕ => a j * Real.exp (-(l j) * (T + δ)) * ((2 * δ * l j) ^ n / n.factorial)) (a j * Real.exp (-(l j) * (T - δ)))`. Introduce `j`. Establish `h1` using `(NormedSpace.expSeries_div_hasSum_exp (2 * δ * l j)).mul_left (a j * Real.exp (-(l j) * (T + δ)))`. Rewrite `h1` using `[← Real.exp_eq_exp_ℝ]`.

Establish `e1 : a j * Real.exp (-(l j) * (T + δ)) * Real.exp (2 * δ * l j) = a j * Real.exp (-(l j) * (T - δ))`. Rewrite using `[mul_assoc, ← Real.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[e1]`.

Conclude with `h1`. Establish `hsumT : Summable (fun i => a i * Real.exp (-(l i) * (T - δ)))`. Use `summable_of_sum_le (fun i => mul_nonneg (ha i) (Real.exp_pos _).le) (c := (F ((T - δ : ℝ) : ℂ)).re) (fun S => ?_)` and prove the remaining obligations. Use `hasSum_le (fun n => ?_) (hasSum_sum (fun j _ => hj j)) hTay` and prove the remaining obligations. Establish `h2` using `(hder n).mul_left ((n.factorial : ℂ)⁻¹ * (((T - δ : ℝ) : ℂ) - ((T + δ : ℝ) : ℂ)) ^ n)`.

Establish `h3` using `Complex.hasSum_re h2`. Establish `e : ∀ j, ((n.factorial : ℂ)⁻¹ * (((T - δ : ℝ) : ℂ) - ((T + δ : ℝ) : ℂ)) ^ n * ((a j : ℂ) * (-(l j : ℂ)) ^ n * Complex.exp (-(l j : ℂ) * ((T + δ : ℝ) : ℂ)))).re = a j * Real.exp (-(l j) * (T + δ)) * ((2 * δ * l j) ^ n / n.factorial)`. Introduce `j`. Rewrite using `[← Complex.ofReal_re (a j * Real.exp (-(l j) * (T + δ)) * ((2 * δ * l j) ^ n / n.factorial))]`. Use `congr 1`.

Use `push_cast`. Establish `: (2 * (δ : ℂ) * (l j : ℂ)) ^ n = ((T : ℂ) - δ - (T + δ)) ^ n * (-(l j : ℂ)) ^ n`. Rewrite using `[← mul_pow]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e] at h3`. Establish `h4` using `sum_le_hasSum S (fun j _ => by have := ha j; have := hl j; positivity) h3`. Simplify `h4` using `only [smul_eq_mul, mul_assoc]`.

Establish `hrealTd : ∀ y : ℝ, T - δ < y → Summable (fun i => a i * Real.exp (-(l i) * y))`. Introduce `y hy`. Use `Summable.of_nonneg_of_le (fun i => mul_nonneg (ha i) (Real.exp_pos _).le) (fun i => ?_) hsumT` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (ha i)`. Establish `hΦTd` using `genDirichlet_differentiableOn a l ha hl (T - δ) hrealTd`.

Establish `hEq2` using `genDirichlet_eqOn_ball_inter hr (by linarith) hFd hΦTd (fun y hy _ => ((hP y hy).tsum_eq).symm)`. Use `⟨T - δ, by linarith, by linarith, fun y hy => ?_⟩` and prove the remaining obligations. Break down `lt_or_ge T y with hyT | hyT` into its components or cases. Conclude with `hP y hyT`. Establish `hs` using `(genDirichlet_summable_of_le a l ha hl (hrealTd y hy) (show y ≤ (y : ℂ).re by rw [Complex.ofReal_re])).hasSum`.

Establish `hmem : (y : ℂ) ∈ Metric.ball (T : ℂ) r ∩ {z : ℂ | T - δ < z.re}`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]`. Apply the tactic sequence `constructor <;> linarith`. Use `show T - δ < (y : ℂ).re`.

Rewrite using `[Complex.ofReal_re]`. Conclude with `hy`. Rewrite using `[hEq2 y hmem]`. Conclude with `hs`.
-/
theorem genDirichlet_landau_step {ι : Type} (a l : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i)
    (F : ℂ → ℂ) (x₀ T : ℝ) (hT : x₀ < T) (hFa : AnalyticAt ℂ F (T : ℂ))
    (hP : ∀ y : ℝ, T < y → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * y)) (F y)) :
    ∃ t, x₀ ≤ t ∧ t < T ∧
      ∀ y : ℝ, t < y → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * y)) (F y) := by
  obtain ⟨r, hr, hFr⟩ := hFa.exists_ball_analyticOnNhd
  have hFd : DifferentiableOn ℂ F (Metric.ball (T : ℂ) r) := hFr.differentiableOn
  have hrealT : ∀ y : ℝ, T < y → Summable (fun i => a i * Real.exp (-(l i) * y)) := by
    intro y hy
    have := (hP y hy).summable
    rw [← Complex.summable_ofReal]
    convert this using 2
    push_cast; rfl
  obtain ⟨δ, hδ0, hδr, hδT⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ r / 4 ∧ δ ≤ (T - x₀) / 2 :=
    ⟨min (r / 4) ((T - x₀) / 2), lt_min (by linarith) (by linarith), min_le_left _ _,
      min_le_right _ _⟩
  have hΦT := genDirichlet_differentiableOn a l ha hl T hrealT
  have hEq1 := genDirichlet_eqOn_ball_inter hr le_rfl hFd hΦT
    (fun y hy _ => ((hP y hy).tsum_eq).symm)
  have hU : IsOpen (Metric.ball (T : ℂ) r ∩ {z : ℂ | T < z.re}) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hcm : ((T + δ : ℝ) : ℂ) ∈ Metric.ball (T : ℂ) r ∩ {z : ℂ | T < z.re} := by
    constructor
    · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    · show T < ((T + δ : ℝ) : ℂ).re
      rw [Complex.ofReal_re]; linarith
  have hev : F =ᶠ[𝓝 ((T + δ : ℝ) : ℂ)]
      (fun z : ℂ => ∑' i, (a i : ℂ) * Complex.exp (-(l i : ℂ) * z)) := by
    filter_upwards [hU.mem_nhds hcm] with z hz using hEq1 z hz
  have hΦsum : ∀ s : ℂ, T < s.re → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * s))
      ((fun z : ℂ => ∑' i, (a i : ℂ) * Complex.exp (-(l i : ℂ) * z)) s) :=
    fun s hs => (genDirichlet_summable_of_le a l ha hl (hrealT s.re hs) le_rfl).hasSum
  have hder : ∀ n : ℕ, HasSum (fun i => (a i : ℂ) * (-(l i : ℂ)) ^ n *
      Complex.exp (-(l i : ℂ) * ((T + δ : ℝ) : ℂ))) (iteratedDeriv n F ((T + δ : ℝ) : ℂ)) := by
    intro n
    rw [hev.iteratedDeriv_eq n]
    exact genDirichlet_hasSum_iteratedDeriv a l _ ha hl T hΦsum n _
      (by rw [Complex.ofReal_re]; linarith)
  have hball : Metric.ball ((T + δ : ℝ) : ℂ) (r - δ) ⊆ Metric.ball (T : ℂ) r := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    have hd : dist ((T + δ : ℝ) : ℂ) (T : ℂ) = δ := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        add_sub_cancel_left, abs_of_pos hδ0]
    calc dist z T ≤ dist z ((T + δ : ℝ) : ℂ) + dist ((T + δ : ℝ) : ℂ) (T : ℂ) := dist_triangle _ _ _
      _ < r := by linarith
  have hz : ((T - δ : ℝ) : ℂ) ∈ Metric.ball ((T + δ : ℝ) : ℂ) (r - δ) := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, show T - δ - (T + δ) = -(2 * δ) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  have hTay := Complex.hasSum_re (Complex.hasSum_taylorSeries_on_ball (hFd.mono hball) hz)
  have hj : ∀ j, HasSum (fun n : ℕ => a j * Real.exp (-(l j) * (T + δ)) *
      ((2 * δ * l j) ^ n / n.factorial)) (a j * Real.exp (-(l j) * (T - δ))) := by
    intro j
    have h1 := (NormedSpace.expSeries_div_hasSum_exp (2 * δ * l j)).mul_left
      (a j * Real.exp (-(l j) * (T + δ)))
    rw [← Real.exp_eq_exp_ℝ] at h1
    have e1 : a j * Real.exp (-(l j) * (T + δ)) * Real.exp (2 * δ * l j)
        = a j * Real.exp (-(l j) * (T - δ)) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    rw [e1] at h1
    exact h1
  have hsumT : Summable (fun i => a i * Real.exp (-(l i) * (T - δ))) := by
    refine summable_of_sum_le (fun i => mul_nonneg (ha i) (Real.exp_pos _).le)
      (c := (F ((T - δ : ℝ) : ℂ)).re) (fun S => ?_)
    refine hasSum_le (fun n => ?_) (hasSum_sum (fun j _ => hj j)) hTay
    have h2 := (hder n).mul_left ((n.factorial : ℂ)⁻¹ * (((T - δ : ℝ) : ℂ) - ((T + δ : ℝ) : ℂ)) ^ n)
    have h3 := Complex.hasSum_re h2
    have e : ∀ j, ((n.factorial : ℂ)⁻¹ * (((T - δ : ℝ) : ℂ) - ((T + δ : ℝ) : ℂ)) ^ n *
        ((a j : ℂ) * (-(l j : ℂ)) ^ n * Complex.exp (-(l j : ℂ) * ((T + δ : ℝ) : ℂ)))).re
        = a j * Real.exp (-(l j) * (T + δ)) * ((2 * δ * l j) ^ n / n.factorial) := by
      intro j
      rw [← Complex.ofReal_re (a j * Real.exp (-(l j) * (T + δ)) * ((2 * δ * l j) ^ n / n.factorial))]
      congr 1
      push_cast
      have : (2 * (δ : ℂ) * (l j : ℂ)) ^ n = ((T : ℂ) - δ - (T + δ)) ^ n * (-(l j : ℂ)) ^ n := by
        rw [← mul_pow]; congr 1; ring
      rw [this]; ring
    simp only [e] at h3
    have h4 := sum_le_hasSum S (fun j _ => by have := ha j; have := hl j; positivity) h3
    simpa only [smul_eq_mul, mul_assoc] using h4
  have hrealTd : ∀ y : ℝ, T - δ < y → Summable (fun i => a i * Real.exp (-(l i) * y)) := by
    intro y hy
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (ha i) (Real.exp_pos _).le)
      (fun i => ?_) hsumT
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (ha i)
  have hΦTd := genDirichlet_differentiableOn a l ha hl (T - δ) hrealTd
  have hEq2 := genDirichlet_eqOn_ball_inter hr (by linarith) hFd hΦTd
    (fun y hy _ => ((hP y hy).tsum_eq).symm)
  refine ⟨T - δ, by linarith, by linarith, fun y hy => ?_⟩
  rcases lt_or_ge T y with hyT | hyT
  · exact hP y hyT
  · have hs := (genDirichlet_summable_of_le a l ha hl (hrealTd y hy)
      (show y ≤ (y : ℂ).re by rw [Complex.ofReal_re])).hasSum
    have hmem : (y : ℂ) ∈ Metric.ball (T : ℂ) r ∩ {z : ℂ | T - δ < z.re} := by
      constructor
      · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_lt]
        constructor <;> linarith
      · show T - δ < (y : ℂ).re
        rw [Complex.ofReal_re]; exact hy
    rw [hEq2 y hmem]
    exact hs

/- English proof (translation)
Set `S : Set ℝ` to `{t | x₀ ≤ t ∧ ∀ y : ℝ, t < y → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * y)) (F y)}`. Establish `hne : S.Nonempty` using `⟨x₁, hx.le, h⟩`. Establish `hbdd : BddBelow S` using `⟨x₀, fun t ht => ht.1⟩`. Establish `hT0 : x₀ ≤ sInf S` using `le_csInf hne (fun t ht => ht.1)`. Establish `hPT : ∀ y : ℝ, sInf S < y → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * y)) (F y)`.

Introduce `y hy`. Take `⟨t, ht, hty⟩` from `exists_lt_of_csInf_lt hne hy`. Conclude with `ht.2 y hty`. Break down `eq_or_lt_of_le hT0 with hE | hlt` into its components or cases. Introduce `x hx0`.

Conclude with `hPT x (by rw [← hE]; exact hx0)`. Take `⟨t, ht0, htT, hPt⟩` from `genDirichlet_landau_step a l ha hl F x₀ (sInf S) hlt (hF _ hlt) hPT`. Conclude with `absurd (csInf_le hbdd ⟨ht0, hPt⟩) (not_le.2 htT)`.
-/
theorem landau_hasSum_of_analyticAt (ι : Type) (a l : ι → ℝ) (x₀ x₁ : ℝ) (F : ℂ → ℂ)
    (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i) (hx : x₀ < x₁)
    (hF : ∀ x : ℝ, x₀ < x → AnalyticAt ℂ F (x : ℂ))
    (h : ∀ x : ℝ, x₁ < x → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * x)) (F x)) :
    ∀ x : ℝ, x₀ < x → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * x)) (F x) := by
  let S : Set ℝ := {t | x₀ ≤ t ∧ ∀ y : ℝ, t < y →
    HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * y)) (F y)}
  have hne : S.Nonempty := ⟨x₁, hx.le, h⟩
  have hbdd : BddBelow S := ⟨x₀, fun t ht => ht.1⟩
  have hT0 : x₀ ≤ sInf S := le_csInf hne (fun t ht => ht.1)
  have hPT : ∀ y : ℝ, sInf S < y →
      HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * y)) (F y) := by
    intro y hy
    obtain ⟨t, ht, hty⟩ := exists_lt_of_csInf_lt hne hy
    exact ht.2 y hty
  rcases eq_or_lt_of_le hT0 with hE | hlt
  · intro x hx0
    exact hPT x (by rw [← hE]; exact hx0)
  · obtain ⟨t, ht0, htT, hPt⟩ :=
      genDirichlet_landau_step a l ha hl F x₀ (sInf S) hlt (hF _ hlt) hPT
    exact absurd (csInf_le hbdd ⟨ht0, hPt⟩) (not_le.2 htT)

/- English proof (translation)
Establish `alg : ∀ (x : ℂ) (p : Σ n : ℕ, Fin n → ι), (((∏ k, a (p.2 k)) / (p.1.factorial : ℝ) : ℝ) : ℂ) * Complex.exp (-((∑ k, l (p.2 k) : ℝ) : ℂ) * x) = (∏ k, (a (p.2 k) : ℂ) * Complex.exp (-(l (p.2 k) : ℂ) * x)) / (p.1.factorial : ℂ)`. Introduce `x p`. Rewrite using `[Finset.prod_mul_distrib, ← Complex.exp_sum]`. Use `push_cast`. Rewrite using `[neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]`.

Simplify using `only [neg_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `key` using `landau_hasSum_of_analyticAt (Σ n : ℕ, Fin n → ι) (fun p => (∏ k, a (p.2 k)) / (p.1.factorial : ℝ)) (fun p => ∑ k, l (p.2 k)) x₀ x₁ G (fun p => div_nonneg (Finset.prod_nonneg fun k _ => ha _) (Nat.cast_nonneg _)) (fun p => Finset.sum_nonneg fun k _ => hl _) hx hG (by`. Introduce `x hx1`. Take `⟨g, hg, hGx⟩` from `h x hx1`.

Rewrite using `[hGx]`. Use `hasSum_tuple_prod_exp _ g hg using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Conclude with `alg _ p)`. Introduce `x hx0`.

Establish `hk` using `key x hx0`. Establish `hinj : Function.Injective (fun i : ι => (⟨1, fun _ => i⟩ : Σ n : ℕ, Fin n → ι))`. Introduce `i j hij`. Use `eq_of_heq (Sigma.mk.inj hij).2` as an intermediate fact. Conclude with `congrFun this 0`.

Establish `hs : Summable (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * x))`. Use `hk.summable.comp_injective hinj` as an intermediate fact. Use `this.congr fun i => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `⟨_, hs.hasSum, ?_⟩` and prove the remaining obligations.

Use `hk.unique ?_` and prove the remaining obligations. Use `hasSum_tuple_prod_exp _ _ hs.hasSum using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Conclude with `alg _ p`.
-/
theorem landau_exp_hasSum_of_analyticAt (ι : Type) (a l : ι → ℝ) (x₀ x₁ : ℝ) (G : ℂ → ℂ)
    (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i) (hx : x₀ < x₁)
    (hG : ∀ x : ℝ, x₀ < x → AnalyticAt ℂ G (x : ℂ))
    (h : ∀ x : ℝ, x₁ < x → ∃ g : ℂ,
      HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * x)) g ∧ G x = Complex.exp g) :
    ∀ x : ℝ, x₀ < x → ∃ g : ℂ,
      HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * x)) g ∧ G x = Complex.exp g := by
  have alg : ∀ (x : ℂ) (p : Σ n : ℕ, Fin n → ι),
      (((∏ k, a (p.2 k)) / (p.1.factorial : ℝ) : ℝ) : ℂ) *
        Complex.exp (-((∑ k, l (p.2 k) : ℝ) : ℂ) * x)
      = (∏ k, (a (p.2 k) : ℂ) * Complex.exp (-(l (p.2 k) : ℂ) * x)) / (p.1.factorial : ℂ) := by
    intro x p
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    push_cast
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    simp only [neg_mul]
    ring
  have key := landau_hasSum_of_analyticAt (Σ n : ℕ, Fin n → ι)
    (fun p => (∏ k, a (p.2 k)) / (p.1.factorial : ℝ)) (fun p => ∑ k, l (p.2 k)) x₀ x₁ G
    (fun p => div_nonneg (Finset.prod_nonneg fun k _ => ha _) (Nat.cast_nonneg _))
    (fun p => Finset.sum_nonneg fun k _ => hl _) hx hG (by
      intro x hx1
      obtain ⟨g, hg, hGx⟩ := h x hx1
      rw [hGx]
      convert hasSum_tuple_prod_exp _ g hg using 1
      funext p
      exact alg _ p)
  intro x hx0
  have hk := key x hx0
  have hinj : Function.Injective (fun i : ι => (⟨1, fun _ => i⟩ : Σ n : ℕ, Fin n → ι)) := by
    intro i j hij
    have := eq_of_heq (Sigma.mk.inj hij).2
    exact congrFun this 0
  have hs : Summable (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * x)) := by
    have := hk.summable.comp_injective hinj
    refine this.congr fun i => ?_
    simp
  refine ⟨_, hs.hasSum, ?_⟩
  refine hk.unique ?_
  convert hasSum_tuple_prod_exp _ _ hs.hasSum using 1
  funext p
  exact alg _ p

end GlobalTheory
