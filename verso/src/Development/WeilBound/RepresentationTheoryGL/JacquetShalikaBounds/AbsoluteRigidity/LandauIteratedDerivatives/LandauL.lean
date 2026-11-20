import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandauSummableOfExpDirichletSeriesEntire

noncomputable section

open Complex Filter Topology

namespace PositivityTheory.RgJS.LandauNonnegativeDirichletSeries

/- English proof (translation)
Use `set δ := (σ - a) / 2 with hδ`. Establish `hδ0 : 0 < δ` using `by rw [hδ]; linarith`. Establish `h1` using `(h (σ - δ) (by rw [hδ]; linarith)).mul_left ((n.factorial : ℝ) / δ ^ n)`. Use `Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) h1` and prove the remaining obligations. Use `hb j` as an intermediate fact.

Use `hμ j` as an intermediate fact. Check the signs of the components of the expression. Establish `h2` using `Real.pow_div_factorial_le_exp (μ j * δ) (mul_nonneg (hμ j) hδ0.le) n`. Establish `hf : (0:ℝ) < n.factorial` using `by positivity`. Establish `h3 : μ j ^ n ≤ (n.factorial : ℝ) / δ ^ n * Real.exp (μ j * δ)`.

Rewrite `h2` using `[div_le_iff₀ hf, mul_pow]`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : Real.exp (-(μ j) * (σ - δ)) = Real.exp (μ j * δ) * Real.exp (-(μ j) * σ)`. Rewrite using `[← Real.exp_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4]`. Establish `h5 : 0 ≤ b j * Real.exp (-(μ j) * σ)` using `mul_nonneg (hb j) (Real.exp_pos _).le`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem summable_pow {ι : Type} (b μ : ι → ℝ) (hb : ∀ j, 0 ≤ b j) (hμ : ∀ j, 0 ≤ μ j) (a : ℝ)
    (h : ∀ σ : ℝ, a < σ → Summable (fun j => b j * Real.exp (-(μ j) * σ))) (n : ℕ) (σ : ℝ) (hσ : a < σ) :
    Summable (fun j => b j * μ j ^ n * Real.exp (-(μ j) * σ)) := by
  set δ := (σ - a) / 2 with hδ
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
Establish `hreal : ∀ σ : ℝ, a < σ → Summable (fun j => b j * Real.exp (-(μ j) * σ))`. Introduce `σ hσ`. Use `(h σ (by simpa using hσ)).summable` as an intermediate fact. Rewrite using `[← Complex.summable_ofReal]`. Use `this using 2` and compare the differences between its conclusion and the goal.

Use `push_cast`. Both sides reduce to the same expression. Proceed by induction on `n generalizing s with`. Consider the case `zero => simpa using h s hs`. Consider the case `succ n ih => set σ := (a + s.re) / 2 with hσ`.

Establish `hσ1 : a < σ` using `by rw [hσ]; linarith`. Establish `hσs : σ < s.re` using `by rw [hσ]; linarith`. Establish `hU : IsOpen {w : ℂ | σ < w.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `key` using `Complex.hasSum_deriv_of_summable_norm (F := fun j w => (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * w)) (U := {w : ℂ | σ < w.re}) (z := s) (summable_pow b μ hb hμ a hreal n σ hσ1) (fun j => by fun_prop) hU (fun j w hw => by`. Establish `hw' : σ < w.re` using `hw`.

Rewrite using `[norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Complex.norm_real, Complex.norm_exp, Real.norm_of_nonneg (hb j), Real.norm_of_nonneg (hμ j)]`. Establish `h0 : 0 ≤ b j * μ j ^ n` using `mul_nonneg (hb j) (pow_nonneg (hμ j) n)`. Use `mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) h0` and prove the remaining obligations. Use `hμ j` as an intermediate fact. Simplify using the standard rewrite rules.

Use the proof step `nlinarith) hσs`. Establish `hev : (fun w : ℂ => ∑' j, (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * w)) =ᶠ[nhds s] iteratedDeriv n F` using `by filter_upwards [hU.mem_nhds hσs] with w hw`. Establish `hw' : σ < w.re` using `hw`. Conclude with `(ih w (by linarith)).tsum_eq`. Rewrite `key` using `[hev.deriv_eq, ← iteratedDeriv_succ]`.

Use `(congrArg (fun f => HasSum f _) (funext fun j => ?_)).mp key` and prove the remaining obligations. Establish `: HasDerivAt (fun w : ℂ => (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * w)) ((b j : ℂ) * (-(μ j : ℂ)) ^ n * (Complex.exp (-(μ j : ℂ) * s) * (-(μ j : ℂ) * 1))) s` using `(((hasDerivAt_id s).const_mul (-(μ j : ℂ))).cexp).const_mul _`. Rewrite using `[this.deriv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasSum_iteratedDeriv {ι : Type} (b μ : ι → ℝ) (F : ℂ → ℂ)
    (hb : ∀ j, 0 ≤ b j) (hμ : ∀ j, 0 ≤ μ j) (a : ℝ)
    (h : ∀ s : ℂ, a < s.re → HasSum (fun j => (b j : ℂ) * Complex.exp (-(μ j : ℂ) * s)) (F s))
    (n : ℕ) (s : ℂ) (hs : a < s.re) :
    HasSum (fun j => (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * s))
      (iteratedDeriv n F s) := by
  have hreal : ∀ σ : ℝ, a < σ → Summable (fun j => b j * Real.exp (-(μ j) * σ)) := by
    intro σ hσ
    have := (h σ (by simpa using hσ)).summable
    rw [← Complex.summable_ofReal]
    convert this using 2
    push_cast; rfl
  induction n generalizing s with
  | zero => simpa using h s hs
  | succ n ih =>
    set σ := (a + s.re) / 2 with hσ
    have hσ1 : a < σ := by rw [hσ]; linarith
    have hσs : σ < s.re := by rw [hσ]; linarith
    have hU : IsOpen {w : ℂ | σ < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have key := Complex.hasSum_deriv_of_summable_norm
      (F := fun j w => (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * w))
      (U := {w : ℂ | σ < w.re}) (z := s)
      (summable_pow b μ hb hμ a hreal n σ hσ1)
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
Establish `key : ∀ σ : ℝ, a < σ → (∃ᶠ z in 𝓝[≠] (σ : ℂ), (f - g) z = 0) → f =ᶠ[𝓝 (σ : ℂ)] g`. Introduce `σ hσ hfr`. Use `((hf σ hσ).sub (hg σ hσ)).frequently_zero_iff_eventually_zero.1 hfr` as an intermediate fact. Use `filter_upwards [this] with z hz`. Conclude with `sub_eq_zero.1 hz`.

Establish `fr : ∀ σ : ℝ, (∀ τ : ℝ, σ < τ → τ < σ + 1 → f τ = g τ) → ∃ᶠ z in 𝓝[≠] (σ : ℂ), (f - g) z = 0`. Introduce `σ hτ`. Establish `h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0)` using `tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)`. Establish `h2 : Tendsto (fun n : ℕ => σ + 1 / ((n : ℝ) + 2)) atTop (𝓝 σ)`. Simplify using `using (tendsto_const_nhds (x := σ)).add h1`.

Establish `ht : Tendsto (fun n : ℕ => ((σ + 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝[≠] (σ : ℂ))`. Use `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ((Complex.continuous_ofReal.tendsto σ).comp h2) (Eventually.of_forall fun n => ?_)` and prove the remaining obligations. Simplify using `only [Set.mem_compl_iff, Set.mem_singleton_iff]`. Introduce `h`. Establish `h3` using `Complex.ofReal_injective h`.

Establish `h4 : (0 : ℝ) < 1 / ((n : ℝ) + 2)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `ht.frequently (Frequently.of_forall fun n => ?_)` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, sub_eq_zero]`. Establish `h4 : (0 : ℝ) < 1 / ((n : ℝ) + 2)` using `by positivity`.

Establish `h5 : 1 / ((n : ℝ) + 2) < 1`. Rewrite using `[div_lt_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]`. Conclude with `hτ _ (by linarith) (by linarith)`. Establish `good : ∀ τ : ℝ, max a b < τ → f =ᶠ[𝓝 (τ : ℂ)] g` using `fun τ hτ => key τ (lt_of_le_of_lt (le_max_left _ _) hτ) (fr τ fun t ht _ => he t (by linarith [le_max_right a b]))`. Introduce `σ hσ`.

Assume the negation of the conclusion as `hne`. Use `set B := {τ : ℝ | a < τ ∧ ¬ (f =ᶠ[𝓝 (τ : ℂ)] g)} with hB`. Establish `hBne : σ ∈ B` using `⟨hσ, hne⟩`. Establish `hBbdd : BddAbove B` using `⟨max a b, fun τ hτ => by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hτ.2 (good τ h)⟩`. Use `set γ := sSup B with hγdef`. Establish `hγσ : σ ≤ γ` using `le_csSup hBbdd hBne`. Establish `hγa : a < γ` using `lt_of_lt_of_le hσ hγσ`.

Establish `above : ∀ τ : ℝ, γ < τ → f =ᶠ[𝓝 (τ : ℂ)] g` using `fun τ hτ => by`. Assume the negation of the conclusion as `h`. Conclude with `absurd (le_csSup hBbdd ⟨by linarith, h⟩) (not_le.2 hτ)`. Establish `hγ : f =ᶠ[𝓝 (γ : ℂ)] g` using `key γ hγa (fr γ fun t ht _ => (above t ht).eq_of_nhds)`. Establish `h1 : ∀ᶠ z in 𝓝 (γ : ℂ), f =ᶠ[𝓝 z] g` using `Filter.Eventually.eventually_nhds hγ`.

Establish `h2 : ∀ᶠ τ in 𝓝 γ, f =ᶠ[𝓝 ((τ : ℝ) : ℂ)] g` using `(Complex.continuous_ofReal.tendsto γ).eventually h1`. Take `⟨δ, hδ, hball⟩` from `Metric.eventually_nhds_iff.1 h2`. Take `⟨τ, hτB, hτ⟩` from `exists_lt_of_lt_csSup ⟨σ, hBne⟩ (show γ - δ < γ by linarith)`. Establish `hτγ : τ ≤ γ` using `le_csSup hBbdd hτB`. Apply the tactic sequence `exact hτB.2 (hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith))`.
-/
theorem propagate (f g : ℂ → ℂ) (a b : ℝ) (hf : ∀ σ : ℝ, a < σ → AnalyticAt ℂ f σ)
    (hg : ∀ σ : ℝ, a < σ → AnalyticAt ℂ g σ) (he : ∀ σ : ℝ, b < σ → f σ = g σ) :
    ∀ σ : ℝ, a < σ → f =ᶠ[𝓝 (σ : ℂ)] g := by
  have key : ∀ σ : ℝ, a < σ → (∃ᶠ z in 𝓝[≠] (σ : ℂ), (f - g) z = 0) → f =ᶠ[𝓝 (σ : ℂ)] g := by
    intro σ hσ hfr
    have := ((hf σ hσ).sub (hg σ hσ)).frequently_zero_iff_eventually_zero.1 hfr
    filter_upwards [this] with z hz
    exact sub_eq_zero.1 hz
  have fr : ∀ σ : ℝ, (∀ τ : ℝ, σ < τ → τ < σ + 1 → f τ = g τ) → ∃ᶠ z in 𝓝[≠] (σ : ℂ), (f - g) z = 0 := by
    intro σ hτ
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    have h2 : Tendsto (fun n : ℕ => σ + 1 / ((n : ℝ) + 2)) atTop (𝓝 σ) := by
      simpa using (tendsto_const_nhds (x := σ)).add h1
    have ht : Tendsto (fun n : ℕ => ((σ + 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝[≠] (σ : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((Complex.continuous_ofReal.tendsto σ).comp h2) (Eventually.of_forall fun n => ?_)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have h3 := Complex.ofReal_injective h
      have h4 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      linarith
    refine ht.frequently (Frequently.of_forall fun n => ?_)
    simp only [Pi.sub_apply, sub_eq_zero]
    have h4 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have h5 : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    exact hτ _ (by linarith) (by linarith)
  have good : ∀ τ : ℝ, max a b < τ → f =ᶠ[𝓝 (τ : ℂ)] g := fun τ hτ =>
    key τ (lt_of_le_of_lt (le_max_left _ _) hτ)
      (fr τ fun t ht _ => he t (by linarith [le_max_right a b]))
  intro σ hσ
  by_contra hne
  set B := {τ : ℝ | a < τ ∧ ¬ (f =ᶠ[𝓝 (τ : ℂ)] g)} with hB
  have hBne : σ ∈ B := ⟨hσ, hne⟩
  have hBbdd : BddAbove B := ⟨max a b, fun τ hτ => by
    by_contra h
    push_neg at h
    exact hτ.2 (good τ h)⟩
  set γ := sSup B with hγdef
  have hγσ : σ ≤ γ := le_csSup hBbdd hBne
  have hγa : a < γ := lt_of_lt_of_le hσ hγσ
  have above : ∀ τ : ℝ, γ < τ → f =ᶠ[𝓝 (τ : ℂ)] g := fun τ hτ => by
    by_contra h
    exact absurd (le_csSup hBbdd ⟨by linarith, h⟩) (not_le.2 hτ)
  have hγ : f =ᶠ[𝓝 (γ : ℂ)] g := key γ hγa (fr γ fun t ht _ => (above t ht).eq_of_nhds)
  have h1 : ∀ᶠ z in 𝓝 (γ : ℂ), f =ᶠ[𝓝 z] g := Filter.Eventually.eventually_nhds hγ
  have h2 : ∀ᶠ τ in 𝓝 γ, f =ᶠ[𝓝 ((τ : ℝ) : ℂ)] g := (Complex.continuous_ofReal.tendsto γ).eventually h1
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h2
  obtain ⟨τ, hτB, hτ⟩ := exists_lt_of_lt_csSup ⟨σ, hBne⟩ (show γ - δ < γ by linarith)
  have hτγ : τ ≤ γ := le_csSup hBbdd hτB
  exact hτB.2 (hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith))

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem re_neg_mul (l : ℝ) (s : ℂ) : (-(l : ℂ) * s).re = -(l * s.re) := by simp

/- English proof (translation)
Establish `mono : ∀ σ τ : ℝ, σ ≤ τ → Summable (fun i => c i * Real.exp (-(l i * σ))) → Summable fun i => c i * Real.exp (-(l i * τ))` using `fun σ τ h hs => hs.of_nonneg_of_le (fun i => mul_nonneg (hc i) (Real.exp_pos _).le) (fun i => mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (hc i))`. Introduce `σ hσ`. Assume the negation of the conclusion as `hns`. Use `set A := {τ : ℝ | σ₀ < τ ∧ Summable fun i => c i * Real.exp (-(l i * τ))} with hA`. Establish `hAne : (max σ₀ σ₁ + 1) ∈ A` using `⟨by linarith [le_max_left σ₀ σ₁], hS _ (by linarith [le_max_right σ₀ σ₁])⟩`.

Establish `hAbdd : BddBelow A` using `⟨σ₀, fun τ hτ => hτ.1.le⟩`. Use `set β := sInf A with hβdef`. Establish `hβσ : σ ≤ β` using `le_csInf ⟨_, hAne⟩ fun τ hτ => by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hns (mono τ σ h.le hτ.2)`. Establish `hβ0 : σ₀ < β` using `lt_of_lt_of_le hσ hβσ`. Take `⟨r, hr, hFr⟩` from `(hF β hβ0).exists_ball_analyticOnNhd`. Use `set ε := min (r / 4) ((β - σ₀) / 2) with hεdef`. Establish `hε : 0 < ε` using `lt_min (by linarith) (by linarith)`.

Establish `hεr : ε ≤ r / 4` using `min_le_left _ _`. Establish `hεβ : ε ≤ (β - σ₀) / 2` using `min_le_right _ _`. Use `set s0 : ℝ := β + ε with hs0`. Take `⟨β', hβ'A, hβ's⟩` from `exists_lt_of_csInf_lt ⟨_, hAne⟩ (show β < s0 by linarith)`. Establish `hββ' : β ≤ β'` using `csInf_le hAbdd hβ'A`.

Use `set G : ℂ → ℂ := fun s => ∑' i, (c i : ℂ) * Complex.exp (-(l i : ℂ) * s) with hG`. Establish `hbd : ∀ i (s : ℂ), β' < s.re → ‖(c i : ℂ) * Complex.exp (-(l i : ℂ) * s)‖ ≤ c i * Real.exp (-(l i * β'))`. Introduce `i s hs`. Rewrite using `[norm_mul, Complex.norm_real, Complex.norm_exp, Real.norm_of_nonneg (hc i), re_neg_mul]`. Conclude with `mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (hc i)`.

Establish `hGsum : ∀ s : ℂ, β' < s.re → HasSum (fun i => (c i : ℂ) * Complex.exp (-(l i : ℂ) * s)) (G s)` using `fun s hs => (Summable.of_norm (hβ'A.2.of_nonneg_of_le (fun i => norm_nonneg _) fun i => hbd i s hs)).hasSum`. Establish `hU : IsOpen {s : ℂ | β' < s.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `hGd : DifferentiableOn ℂ G {s : ℂ | β' < s.re}` using `differentiableOn_tsum_of_summable_norm hβ'A.2 (fun i => by fun_prop) hU (fun i w hw => hbd i w hw)`. Establish `hGa : ∀ τ : ℝ, β' < τ → AnalyticAt ℂ G τ` using `fun τ hτ => hGd.analyticAt (hU.mem_nhds (by simpa using hτ))`. Establish `hFG : ∀ τ : ℝ, σ₁ < τ → F τ = G τ`.

Introduce `τ hτ`. Rewrite using `[hE τ hτ, hG]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Use `push_cast`.

Put the polynomial expressions in normal form. Establish `hev : F =ᶠ[𝓝 ((s0 : ℝ) : ℂ)] G` using `propagate F G β' σ₁ (fun τ hτ => hF τ (by linarith)) hGa hFG s0 hβ's`. Establish `hFd : DifferentiableOn ℂ F (Metric.ball ((s0 : ℝ) : ℂ) (3 * r / 4))`. Introduce `w hw`. Use `(hFr w ?_).differentiableAt.differentiableWithinAt` and prove the remaining obligations.

Rewrite `hw`, the goal using `[Metric.mem_ball]`. Establish `: dist w (β : ℂ) ≤ dist w ((s0 : ℝ) : ℂ) + dist ((s0 : ℝ) : ℂ) (β : ℂ)` using `dist_triangle _ _ _`. Establish `h2 : dist ((s0 : ℝ) : ℂ) (β : ℂ) = ε`. Rewrite using `[Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hs0]`. Rewrite using `[show β + ε - β = ε by ring, abs_of_pos hε]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set z : ℝ := β - ε with hz`. Establish `hzb : ((z : ℝ) : ℂ) ∈ Metric.ball ((s0 : ℝ) : ℂ) (3 * r / 4)`. Rewrite using `[Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hz, hs0, show β - ε - (β + ε) = -(2 * ε) by ring, abs_neg, abs_of_pos (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hT` using `Complex.hasSum_re (Complex.hasSum_taylorSeries_on_ball hFd hzb)`. Establish `hder : ∀ n : ℕ, HasSum (fun i => (c i : ℂ) * (-(l i : ℂ)) ^ n * Complex.exp (-(l i : ℂ) * ((s0 : ℝ) : ℂ))) (iteratedDeriv n F ((s0 : ℝ) : ℂ))`. Introduce `n`. Rewrite using `[hev.iteratedDeriv_eq n]`. Conclude with `hasSum_iteratedDeriv c l G hc hl β' hGsum n _ (by simpa using hβ's)`.

Establish `hj : ∀ i, HasSum (fun n : ℕ => c i * Real.exp (-(l i * s0)) * ((2 * ε * l i) ^ n / n.factorial)) (c i * Real.exp (-(l i * z)))`. Introduce `i`. Establish `h1` using `(NormedSpace.expSeries_div_hasSum_exp (2 * ε * l i)).mul_left (c i * Real.exp (-(l i * s0)))`. Rewrite `h1` using `[← Real.exp_eq_exp_ℝ]`. Establish `e : c i * Real.exp (-(l i * z)) = c i * Real.exp (-(l i * s0)) * Real.exp (2 * ε * l i)`.

Rewrite using `[mul_assoc, ← Real.exp_add]`. Use `congr 2`. Rewrite using `[hz, hs0]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `h1`. Establish `hzA : Summable fun i => c i * Real.exp (-(l i * z))`. Use `summable_of_sum_le (fun i => mul_nonneg (hc i) (Real.exp_pos _).le) (c := (F z).re) (fun S => ?_)` and prove the remaining obligations. Use `hasSum_le (fun n => ?_) (hasSum_sum (fun i _ => hj i)) hT` and prove the remaining obligations. Establish `h2` using `Complex.hasSum_re ((hder n).mul_left ((n.factorial : ℂ)⁻¹ * (((z : ℝ) : ℂ) - ((s0 : ℝ) : ℂ)) ^ n))`.

Establish `e : ∀ i, ((n.factorial : ℂ)⁻¹ * (((z : ℝ) : ℂ) - ((s0 : ℝ) : ℂ)) ^ n * ((c i : ℂ) * (-(l i : ℂ)) ^ n * Complex.exp (-(l i : ℂ) * ((s0 : ℝ) : ℂ)))).re = c i * Real.exp (-(l i * s0)) * ((2 * ε * l i) ^ n / n.factorial)`. Introduce `i`. Rewrite using `[← Complex.ofReal_re (c i * Real.exp (-(l i * s0)) * ((2 * ε * l i) ^ n / n.factorial))]`. Use `congr 1`. Establish `hzs : ((z : ℝ) : ℂ) - ((s0 : ℝ) : ℂ) = ((-(2 * ε) : ℝ) : ℂ)`.

Rewrite using `[← Complex.ofReal_sub, hz, hs0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hzs]`. Use `push_cast`.

Establish `: ((-(2 * (ε : ℂ))) ^ n) * (-(l i : ℂ)) ^ n = (2 * (ε : ℂ) * (l i : ℂ)) ^ n`. Rewrite using `[← mul_pow]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[show Complex.exp (-(l i : ℂ) * (s0 : ℂ)) = Complex.exp (-((l i : ℂ) * (s0 : ℂ))) by ring_nf]`.

Take the linear combination `(↑(n.factorial : ℕ) : ℂ)⁻¹ * (c i : ℂ) * Complex.exp (-((l i : ℂ) * (s0 : ℂ))) * this`. Simplify using `only [e] at h2`. Establish `h4` using `sum_le_hasSum S (fun i _ => by have := hc i; have := hl i; positivity) h2`. Establish `e2 : (((n.factorial : ℂ)⁻¹ • (((z : ℝ) : ℂ) - ((s0 : ℝ) : ℂ)) ^ n • iteratedDeriv n F ((s0 : ℝ) : ℂ))).re = ((n.factorial : ℂ)⁻¹ * (((z : ℝ) : ℂ) - ((s0 : ℝ) : ℂ)) ^ n * iteratedDeriv n F ((s0 : ℝ) : ℂ)).re`. Simplify using `only [smul_eq_mul, mul_assoc]`.

Rewrite using `[e2]`. Conclude with `h4`. Establish `hzA' : z ∈ A` using `⟨by linarith, hzA⟩`. Use `csInf_le hAbdd hzA'` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem linL (I : Type) (c l : I → ℝ) (σ₀ σ₁ : ℝ) (F : ℂ → ℂ) (hc : ∀ i, 0 ≤ c i) (hl : ∀ i, 0 ≤ l i)
    (hF : ∀ σ : ℝ, σ₀ < σ → AnalyticAt ℂ F σ)
    (hS : ∀ σ : ℝ, σ₁ < σ → Summable fun i => c i * Real.exp (-(l i * σ)))
    (hE : ∀ σ : ℝ, σ₁ < σ → F σ = ∑' i, ((c i * Real.exp (-(l i * σ)) : ℝ) : ℂ)) :
    ∀ σ : ℝ, σ₀ < σ → Summable fun i => c i * Real.exp (-(l i * σ)) := by
  have mono : ∀ σ τ : ℝ, σ ≤ τ → Summable (fun i => c i * Real.exp (-(l i * σ))) →
      Summable fun i => c i * Real.exp (-(l i * τ)) :=
    fun σ τ h hs => hs.of_nonneg_of_le (fun i => mul_nonneg (hc i) (Real.exp_pos _).le)
      (fun i => mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (hc i))
  intro σ hσ
  by_contra hns
  set A := {τ : ℝ | σ₀ < τ ∧ Summable fun i => c i * Real.exp (-(l i * τ))} with hA
  have hAne : (max σ₀ σ₁ + 1) ∈ A :=
    ⟨by linarith [le_max_left σ₀ σ₁], hS _ (by linarith [le_max_right σ₀ σ₁])⟩
  have hAbdd : BddBelow A := ⟨σ₀, fun τ hτ => hτ.1.le⟩
  set β := sInf A with hβdef
  have hβσ : σ ≤ β := le_csInf ⟨_, hAne⟩ fun τ hτ => by
    by_contra h
    push_neg at h
    exact hns (mono τ σ h.le hτ.2)
  have hβ0 : σ₀ < β := lt_of_lt_of_le hσ hβσ
  obtain ⟨r, hr, hFr⟩ := (hF β hβ0).exists_ball_analyticOnNhd
  set ε := min (r / 4) ((β - σ₀) / 2) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεr : ε ≤ r / 4 := min_le_left _ _
  have hεβ : ε ≤ (β - σ₀) / 2 := min_le_right _ _
  set s0 : ℝ := β + ε with hs0
  obtain ⟨β', hβ'A, hβ's⟩ := exists_lt_of_csInf_lt ⟨_, hAne⟩ (show β < s0 by linarith)
  have hββ' : β ≤ β' := csInf_le hAbdd hβ'A
  set G : ℂ → ℂ := fun s => ∑' i, (c i : ℂ) * Complex.exp (-(l i : ℂ) * s) with hG
  have hbd : ∀ i (s : ℂ), β' < s.re → ‖(c i : ℂ) * Complex.exp (-(l i : ℂ) * s)‖ ≤ c i * Real.exp (-(l i * β')) := by
    intro i s hs
    rw [norm_mul, Complex.norm_real, Complex.norm_exp, Real.norm_of_nonneg (hc i), re_neg_mul]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (hc i)
  have hGsum : ∀ s : ℂ, β' < s.re → HasSum (fun i => (c i : ℂ) * Complex.exp (-(l i : ℂ) * s)) (G s) :=
    fun s hs => (Summable.of_norm (hβ'A.2.of_nonneg_of_le (fun i => norm_nonneg _) fun i => hbd i s hs)).hasSum
  have hU : IsOpen {s : ℂ | β' < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hGd : DifferentiableOn ℂ G {s : ℂ | β' < s.re} :=
    differentiableOn_tsum_of_summable_norm hβ'A.2 (fun i => by fun_prop) hU (fun i w hw => hbd i w hw)
  have hGa : ∀ τ : ℝ, β' < τ → AnalyticAt ℂ G τ := fun τ hτ =>
    hGd.analyticAt (hU.mem_nhds (by simpa using hτ))
  have hFG : ∀ τ : ℝ, σ₁ < τ → F τ = G τ := by
    intro τ hτ
    rw [hE τ hτ, hG]
    congr 1
    funext i
    push_cast
    ring_nf
  have hev : F =ᶠ[𝓝 ((s0 : ℝ) : ℂ)] G :=
    propagate F G β' σ₁ (fun τ hτ => hF τ (by linarith)) hGa hFG s0 hβ's
  have hFd : DifferentiableOn ℂ F (Metric.ball ((s0 : ℝ) : ℂ) (3 * r / 4)) := by
    intro w hw
    refine (hFr w ?_).differentiableAt.differentiableWithinAt
    rw [Metric.mem_ball] at hw ⊢
    have : dist w (β : ℂ) ≤ dist w ((s0 : ℝ) : ℂ) + dist ((s0 : ℝ) : ℂ) (β : ℂ) := dist_triangle _ _ _
    have h2 : dist ((s0 : ℝ) : ℂ) (β : ℂ) = ε := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hs0]
      rw [show β + ε - β = ε by ring, abs_of_pos hε]
    linarith
  set z : ℝ := β - ε with hz
  have hzb : ((z : ℝ) : ℂ) ∈ Metric.ball ((s0 : ℝ) : ℂ) (3 * r / 4) := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hz, hs0,
      show β - ε - (β + ε) = -(2 * ε) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  have hT := Complex.hasSum_re (Complex.hasSum_taylorSeries_on_ball hFd hzb)
  have hder : ∀ n : ℕ, HasSum (fun i => (c i : ℂ) * (-(l i : ℂ)) ^ n * Complex.exp (-(l i : ℂ) * ((s0 : ℝ) : ℂ)))
      (iteratedDeriv n F ((s0 : ℝ) : ℂ)) := by
    intro n
    rw [hev.iteratedDeriv_eq n]
    exact hasSum_iteratedDeriv c l G hc hl β' hGsum n _ (by simpa using hβ's)
  have hj : ∀ i, HasSum (fun n : ℕ => c i * Real.exp (-(l i * s0)) * ((2 * ε * l i) ^ n / n.factorial))
      (c i * Real.exp (-(l i * z))) := by
    intro i
    have h1 := (NormedSpace.expSeries_div_hasSum_exp (2 * ε * l i)).mul_left (c i * Real.exp (-(l i * s0)))
    rw [← Real.exp_eq_exp_ℝ] at h1
    have e : c i * Real.exp (-(l i * z)) = c i * Real.exp (-(l i * s0)) * Real.exp (2 * ε * l i) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      rw [hz, hs0]; ring
    rw [e]
    exact h1
  have hzA : Summable fun i => c i * Real.exp (-(l i * z)) := by
    refine summable_of_sum_le (fun i => mul_nonneg (hc i) (Real.exp_pos _).le) (c := (F z).re) (fun S => ?_)
    refine hasSum_le (fun n => ?_) (hasSum_sum (fun i _ => hj i)) hT
    have h2 := Complex.hasSum_re ((hder n).mul_left ((n.factorial : ℂ)⁻¹ * (((z : ℝ) : ℂ) - ((s0 : ℝ) : ℂ)) ^ n))
    have e : ∀ i, ((n.factorial : ℂ)⁻¹ * (((z : ℝ) : ℂ) - ((s0 : ℝ) : ℂ)) ^ n *
        ((c i : ℂ) * (-(l i : ℂ)) ^ n * Complex.exp (-(l i : ℂ) * ((s0 : ℝ) : ℂ)))).re =
        c i * Real.exp (-(l i * s0)) * ((2 * ε * l i) ^ n / n.factorial) := by
      intro i
      rw [← Complex.ofReal_re (c i * Real.exp (-(l i * s0)) * ((2 * ε * l i) ^ n / n.factorial))]
      congr 1
      have hzs : ((z : ℝ) : ℂ) - ((s0 : ℝ) : ℂ) = ((-(2 * ε) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_sub, hz, hs0]; congr 1; ring
      rw [hzs]
      push_cast
      have : ((-(2 * (ε : ℂ))) ^ n) * (-(l i : ℂ)) ^ n = (2 * (ε : ℂ) * (l i : ℂ)) ^ n := by
        rw [← mul_pow]; congr 1; ring
      rw [show Complex.exp (-(l i : ℂ) * (s0 : ℂ)) = Complex.exp (-((l i : ℂ) * (s0 : ℂ))) by ring_nf]
      linear_combination (↑(n.factorial : ℕ) : ℂ)⁻¹ * (c i : ℂ) * Complex.exp (-((l i : ℂ) * (s0 : ℂ))) * this
    simp only [e] at h2
    have h4 := sum_le_hasSum S (fun i _ => by have := hc i; have := hl i; positivity) h2
    have e2 : (((n.factorial : ℂ)⁻¹ • (((z : ℝ) : ℂ) - ((s0 : ℝ) : ℂ)) ^ n • iteratedDeriv n F ((s0 : ℝ) : ℂ))).re =
        ((n.factorial : ℂ)⁻¹ * (((z : ℝ) : ℂ) - ((s0 : ℝ) : ℂ)) ^ n * iteratedDeriv n F ((s0 : ℝ) : ℂ)).re := by
      simp only [smul_eq_mul, mul_assoc]
    rw [e2]
    exact h4
  have hzA' : z ∈ A := ⟨by linarith, hzA⟩
  have := csInf_le hAbdd hzA'
  linarith

end PositivityTheory.RgJS.LandauNonnegativeDirichletSeries

namespace PositivityTheory.RgJS

open LandauNonnegativeDirichletSeries

/- English proof (translation)
Introduce `I c l σ₀ σ₁ F hc hl hF hS hE`. Use `set P := Σ n : ℕ, Fin n → I`. Use `set C : P → ℝ := fun p => (∏ k, c (p.2 k)) / (p.1.factorial : ℝ) with hC`. Use `set L : P → ℝ := fun p => ∑ k, l (p.2 k) with hL`. Establish `hC0 : ∀ p, 0 ≤ C p` using `fun p => div_nonneg (Finset.prod_nonneg fun k _ => hc _) (Nat.cast_nonneg _)`.

Establish `hL0 : ∀ p, 0 ≤ L p` using `fun p => Finset.sum_nonneg fun k _ => hl _`. Establish `hterm : ∀ σ : ℝ, ∀ p : P, (∏ k, (((c (p.2 k) * Real.exp (-(l (p.2 k) * σ)) : ℝ)) : ℂ)) / (p.1.factorial : ℂ) = ((C p * Real.exp (-(L p * σ)) : ℝ) : ℂ)`. Introduce `σ p`. Simplify using `only [hC, hL]`. Use `push_cast`.

Rewrite using `[Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.sum_mul, Finset.sum_neg_distrib]`. Expand and normalize the polynomial expressions, which then agree. Establish `hexp : ∀ σ : ℝ, σ₁ < σ → HasSum (fun p : P => ((C p * Real.exp (-(L p * σ)) : ℝ) : ℂ)) ((Real.exp (∑' i, c i * Real.exp (-(l i * σ))) : ℝ) : ℂ)`. Introduce `σ hσ`. Establish `h1 : HasSum (fun i => ((c i * Real.exp (-(l i * σ)) : ℝ) : ℂ)) ((∑' i, c i * Real.exp (-(l i * σ)) : ℝ) : ℂ)` using `(Complex.hasSum_ofReal).2 (hS σ hσ).hasSum`.

Establish `h2` using `GlobalTheory.hasSum_tuple_prod_exp _ _ h1`. Rewrite `h2` using `[← Complex.ofReal_exp]`. Simplify `h2` using `only [hterm σ]`. Establish `key` using `linL P C L σ₀ σ₁ F hC0 hL0 hF (fun σ hσ => (Complex.hasSum_ofReal.1 (hexp σ hσ)).summable) (fun σ hσ => by rw [hE σ hσ]; exact (hexp σ hσ).tsum_eq.symm)`. Introduce `σ hσ`.

Establish `hinj : Function.Injective (fun i : I => (⟨1, fun _ => i⟩ : P))`. Introduce `i j hij`. Use `eq_of_heq (Sigma.mk.inj hij).2` as an intermediate fact. Conclude with `congrFun this 0`. Use `(key σ hσ).comp_injective hinj` as an intermediate fact.

Use `this.congr fun i => ?_` and prove the remaining obligations. Simplify using `[hC, hL]`.
-/
theorem landauL : LandauL := by
  intro I c l σ₀ σ₁ F hc hl hF hS hE
  set P := Σ n : ℕ, Fin n → I
  set C : P → ℝ := fun p => (∏ k, c (p.2 k)) / (p.1.factorial : ℝ) with hC
  set L : P → ℝ := fun p => ∑ k, l (p.2 k) with hL
  have hC0 : ∀ p, 0 ≤ C p := fun p => div_nonneg (Finset.prod_nonneg fun k _ => hc _) (Nat.cast_nonneg _)
  have hL0 : ∀ p, 0 ≤ L p := fun p => Finset.sum_nonneg fun k _ => hl _
  have hterm : ∀ σ : ℝ, ∀ p : P, (∏ k, (((c (p.2 k) * Real.exp (-(l (p.2 k) * σ)) : ℝ)) : ℂ)) / (p.1.factorial : ℂ) =
      ((C p * Real.exp (-(L p * σ)) : ℝ) : ℂ) := by
    intro σ p
    simp only [hC, hL]
    push_cast
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.sum_mul, Finset.sum_neg_distrib]
    ring
  have hexp : ∀ σ : ℝ, σ₁ < σ → HasSum (fun p : P => ((C p * Real.exp (-(L p * σ)) : ℝ) : ℂ))
      ((Real.exp (∑' i, c i * Real.exp (-(l i * σ))) : ℝ) : ℂ) := by
    intro σ hσ
    have h1 : HasSum (fun i => ((c i * Real.exp (-(l i * σ)) : ℝ) : ℂ)) ((∑' i, c i * Real.exp (-(l i * σ)) : ℝ) : ℂ) :=
      (Complex.hasSum_ofReal).2 (hS σ hσ).hasSum
    have h2 := GlobalTheory.hasSum_tuple_prod_exp _ _ h1
    rw [← Complex.ofReal_exp] at h2
    simpa only [hterm σ] using h2
  have key := linL P C L σ₀ σ₁ F hC0 hL0 hF
    (fun σ hσ => (Complex.hasSum_ofReal.1 (hexp σ hσ)).summable)
    (fun σ hσ => by rw [hE σ hσ]; exact (hexp σ hσ).tsum_eq.symm)
  intro σ hσ
  have hinj : Function.Injective (fun i : I => (⟨1, fun _ => i⟩ : P)) := by
    intro i j hij
    have := eq_of_heq (Sigma.mk.inj hij).2
    exact congrFun this 0
  have := (key σ hσ).comp_injective hinj
  refine this.congr fun i => ?_
  simp [hC, hL]

end PositivityTheory.RgJS
