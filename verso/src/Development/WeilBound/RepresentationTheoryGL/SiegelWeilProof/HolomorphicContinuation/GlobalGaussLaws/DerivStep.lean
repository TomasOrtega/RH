import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DilDSt

noncomputable section

open Topology Metric

namespace PositivityTheory.Rg.Sw.Glob

namespace DilDH

variable {E : Type} [MetricSpace E] [ProperSpace E]

/- English proof (translation)
Introduce `p hp`. Take `⟨z0, u0⟩` from `p`. Establish `hz0 : z0 ∈ U` using `hp.1`. Establish `hopen : IsOpen (U ×ˢ (Set.univ : Set E))` using `hU.prod isOpen_univ`. Apply `ContinuousAt.continuousWithinAt` to reduce the goal to its premises.

Take `⟨R, hR, hRU⟩` from `Metric.isOpen_iff.1 hU z0 hz0`. Use `set r := R / 4 with hr`. Establish `hr0 : 0 < r` using `by positivity`. Establish `hK : closedBall z0 (2 * r) ⊆ U` using `(closedBall_subset_ball (by linarith)).trans hRU`. Rewrite using `[Metric.continuousAt_iff']`.

Introduce `ε hε`. Establish `hunif : ∀ᶠ u in 𝓝 u0, ∀ w ∈ closedBall z0 (2 * r), dist (g w u) (g w u0) < ε * r / 2`. Apply `(isCompact_closedBall z0 (2 * r)).eventually_forall_of_forall_eventually` to reduce the goal to its premises. Introduce `w hw`. Establish `hwU : w ∈ U` using `hK hw`.

Establish `hcont : ContinuousAt (fun p : ℂ × E => g p.1 p.2) (w, u0)` using `hc.continuousAt (hopen.mem_nhds ⟨hwU, trivial⟩)`. Establish `h1 : Filter.Tendsto (fun q : E × ℂ => g q.2 q.1) (𝓝 (u0, w)) (𝓝 (g w u0))` using `hcont.tendsto.comp (continuous_swap.tendsto (u0, w))`. Establish `h2 : Filter.Tendsto (fun q : E × ℂ => g q.2 u0) (𝓝 (u0, w)) (𝓝 (g w u0))` using `hcont.tendsto.comp ((continuous_snd.prodMk continuous_const).tendsto (u0, w))`. Establish `hε' : 0 < ε * r / 4` using `by positivity`. Use `filter_upwards [Metric.tendsto_nhds.1 h1 _ hε', Metric.tendsto_nhds.1 h2 _ hε'] with q hq1 hq2`.

Combine the equalities or inequalities in the displayed calculation. Establish `hd0 : ContinuousAt (deriv fun z => g z u0) z0` using `((hd u0).deriv hU).continuousOn.continuousAt (hU.mem_nhds hz0)`. Establish `e1` using `(continuous_fst.tendsto (z0, u0)).eventually (Metric.tendsto_nhds.1 hd0 (ε / 2) (by positivity))`. Establish `e2` using `(continuous_fst.tendsto (z0, u0)).eventually (Metric.ball_mem_nhds z0 hr0)`. Establish `e3` using `(continuous_snd.tendsto (z0, u0)).eventually hunif`.

Use `filter_upwards [e1, e2, e3] with q hq1 hq2 hq3`. Take `⟨z, u⟩` from `q`. Simplify using `only at hq1 hq2 hq3 ⊢`. Establish `hzU : closedBall z r ⊆ closedBall z0 (2 * r)`. Introduce `w hw`.

Rewrite `hw`, the goal using `[mem_closedBall]`. Combine the equalities or inequalities in the displayed calculation. Establish `hcu : deriv (fun z => g z u) z = Complex.cderiv r (fun z => g z u) z` using `(Complex.cderiv_eq_deriv hU (hd u) hr0 (hzU.trans hK)).symm`. Establish `hcu0 : deriv (fun z => g z u0) z = Complex.cderiv r (fun z => g z u0) z` using `(Complex.cderiv_eq_deriv hU (hd u0) hr0 (hzU.trans hK)).symm`. Establish `hsph : sphere z r ⊆ U` using `sphere_subset_closedBall.trans (hzU.trans hK)`.

Establish `hdiff : dist (Complex.cderiv r (fun z => g z u) z) (Complex.cderiv r (fun z => g z u0) z) < ε * r / 2 / r`. Rewrite using `[dist_eq_norm]`. Apply `Complex.norm_cderiv_sub_lt hr0` to reduce the goal to its premises. Introduce `w hw`. Rewrite using `[← dist_eq_norm]`.

Conclude with `hq3 w (hzU (sphere_subset_closedBall hw))`. Conclude with `(hd u).continuousOn.mono hsph`. Conclude with `(hd u0).continuousOn.mono hsph`. Establish `hhalf : ε * r / 2 / r = ε / 2` using `by field_simp`. Rewrite `hdiff` using `[hhalf]`.

Establish `hfirst : dist (deriv (fun z => g z u) z) (deriv (fun z => g z u0) z) < ε / 2`. Rewrite using `[hcu, hcu0]`. Conclude with `hdiff`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem deriv_step {U : Set ℂ} (hU : IsOpen U) {g : ℂ → E → ℂ}
    (hc : ContinuousOn (fun p : ℂ × E => g p.1 p.2) (U ×ˢ Set.univ))
    (hd : ∀ u, DifferentiableOn ℂ (fun z => g z u) U) :
    ContinuousOn (fun p : ℂ × E => deriv (fun z => g z p.2) p.1) (U ×ˢ Set.univ) := by
  intro p hp
  obtain ⟨z0, u0⟩ := p
  have hz0 : z0 ∈ U := hp.1
  have hopen : IsOpen (U ×ˢ (Set.univ : Set E)) := hU.prod isOpen_univ
  apply ContinuousAt.continuousWithinAt
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU z0 hz0
  set r := R / 4 with hr
  have hr0 : 0 < r := by positivity
  have hK : closedBall z0 (2 * r) ⊆ U := (closedBall_subset_ball (by linarith)).trans hRU
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hunif : ∀ᶠ u in 𝓝 u0, ∀ w ∈ closedBall z0 (2 * r), dist (g w u) (g w u0) < ε * r / 2 := by
    apply (isCompact_closedBall z0 (2 * r)).eventually_forall_of_forall_eventually
    intro w hw
    have hwU : w ∈ U := hK hw
    have hcont : ContinuousAt (fun p : ℂ × E => g p.1 p.2) (w, u0) :=
      hc.continuousAt (hopen.mem_nhds ⟨hwU, trivial⟩)
    have h1 : Filter.Tendsto (fun q : E × ℂ => g q.2 q.1) (𝓝 (u0, w)) (𝓝 (g w u0)) :=
      hcont.tendsto.comp (continuous_swap.tendsto (u0, w))
    have h2 : Filter.Tendsto (fun q : E × ℂ => g q.2 u0) (𝓝 (u0, w)) (𝓝 (g w u0)) :=
      hcont.tendsto.comp ((continuous_snd.prodMk continuous_const).tendsto (u0, w))
    have hε' : 0 < ε * r / 4 := by positivity
    filter_upwards [Metric.tendsto_nhds.1 h1 _ hε', Metric.tendsto_nhds.1 h2 _ hε'] with q hq1 hq2
    calc dist (g q.2 q.1) (g q.2 u0)
        ≤ dist (g q.2 q.1) (g w u0) + dist (g q.2 u0) (g w u0) := dist_triangle_right _ _ _
      _ < ε * r / 4 + ε * r / 4 := add_lt_add hq1 hq2
      _ = ε * r / 2 := by ring
  have hd0 : ContinuousAt (deriv fun z => g z u0) z0 :=
    ((hd u0).deriv hU).continuousOn.continuousAt (hU.mem_nhds hz0)
  have e1 := (continuous_fst.tendsto (z0, u0)).eventually
    (Metric.tendsto_nhds.1 hd0 (ε / 2) (by positivity))
  have e2 := (continuous_fst.tendsto (z0, u0)).eventually (Metric.ball_mem_nhds z0 hr0)
  have e3 := (continuous_snd.tendsto (z0, u0)).eventually hunif
  filter_upwards [e1, e2, e3] with q hq1 hq2 hq3
  obtain ⟨z, u⟩ := q
  simp only at hq1 hq2 hq3 ⊢
  have hzU : closedBall z r ⊆ closedBall z0 (2 * r) := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    calc dist w z0 ≤ dist w z + dist z z0 := dist_triangle _ _ _
      _ ≤ r + r := add_le_add hw hq2.le
      _ = 2 * r := by ring
  have hcu : deriv (fun z => g z u) z = Complex.cderiv r (fun z => g z u) z :=
    (Complex.cderiv_eq_deriv hU (hd u) hr0 (hzU.trans hK)).symm
  have hcu0 : deriv (fun z => g z u0) z = Complex.cderiv r (fun z => g z u0) z :=
    (Complex.cderiv_eq_deriv hU (hd u0) hr0 (hzU.trans hK)).symm
  have hsph : sphere z r ⊆ U := sphere_subset_closedBall.trans (hzU.trans hK)
  have hdiff : dist (Complex.cderiv r (fun z => g z u) z) (Complex.cderiv r (fun z => g z u0) z)
      < ε * r / 2 / r := by
    rw [dist_eq_norm]
    apply Complex.norm_cderiv_sub_lt hr0
    · intro w hw
      rw [← dist_eq_norm]
      exact hq3 w (hzU (sphere_subset_closedBall hw))
    · exact (hd u).continuousOn.mono hsph
    · exact (hd u0).continuousOn.mono hsph
  have hhalf : ε * r / 2 / r = ε / 2 := by field_simp
  rw [hhalf] at hdiff
  have hfirst : dist (deriv (fun z => g z u) z) (deriv (fun z => g z u0) z) < ε / 2 := by
    rw [hcu, hcu0]
    exact hdiff
  calc dist (deriv (fun z => g z u) z) (deriv (fun z => g z u0) z0)
      ≤ dist (deriv (fun z => g z u) z) (deriv (fun z => g z u0) z)
        + dist (deriv (fun z => g z u0) z) (deriv (fun z => g z u0) z0) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hfirst hq1
    _ = ε := by ring

def scaleL (m n : ℕ) (s : ℝ) (X : Fin n → ℝ) : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ) where
  toFun u := fun i j => u i j * (Real.exp (s * X j) : ℂ)
  invFun u := fun i j => u i j * (Real.exp (-(s * X j)) : ℂ)
  map_add' u v := by funext i j; simp [add_mul]
  map_smul' r u := by funext i j; simp [Complex.real_smul, mul_assoc]
  left_inv u := by
    funext i j
    simp only [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one,
      mul_one]
  right_inv u := by
    funext i j
    simp only [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one,
      mul_one]

end DilDH

/- English proof (translation)
Introduce `m n f s X a hf`. Take `⟨S, hS⟩` from `hf`. Use `⟨a • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (DilDH.scaleL m n s X).toContinuousLinearEquiv S, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `u`. Simplify using `only [SchwartzMap.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, smul_eq_mul, ← hS]`.

Both sides reduce to the same expression.
-/
theorem schScale : SchScale := by
  intro m n f s X a hf
  obtain ⟨S, hS⟩ := hf
  refine ⟨a • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (DilDH.scaleL m n s X).toContinuousLinearEquiv S, ?_⟩
  funext u
  simp only [SchwartzMap.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, smul_eq_mul, ← hS]
  rfl

/- English proof (translation)
Introduce `m n U hU f hc hd r`. Proceed by induction on `r generalizing f with`. Consider the case `zero => simpa only [iteratedDeriv_zero] using hc`. Consider the case `succ k ih`. Establish `h1` using `DilDH.deriv_step hU hc hd`.

Establish `h2 : ∀ u, DifferentiableOn ℂ (fun z => deriv (fun z => f z u) z) U` using `fun u => (hd u).deriv hU`. Establish `h3` using `ih (fun z u => deriv (fun z => f z u) z) h1 h2`. Simplify `h3` using `only [iteratedDeriv_succ']`.
-/
theorem contDeriv : ContDeriv := by
  intro m n U hU f hc hd r
  induction r generalizing f with
  | zero => simpa only [iteratedDeriv_zero] using hc
  | succ k ih =>
    have h1 := DilDH.deriv_step hU hc hd
    have h2 : ∀ u, DifferentiableOn ℂ (fun z => deriv (fun z => f z u) z) U :=
      fun u => (hd u).deriv hU
    have h3 := ih (fun z u => deriv (fun z => f z u) z) h1 h2
    simpa only [iteratedDeriv_succ'] using h3

end PositivityTheory.Rg.Sw.Glob
