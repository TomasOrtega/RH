import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloContDiffStatement
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.IntegralMollProfBall

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff Convolution

/- English proof (translation)
Use function extensionality and compare the values at `x`. Rewrite using `[convolution_eq_swap]`. Simplify using `only [mollify, ContinuousLinearMap.lsmul_apply, Complex.real_smul]`.
-/
theorem mollify_eq_convolution (n : ℕ) (t : ℝ) (u : V n → ℂ) :
    mollify n t u = (moll n t) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u := by
  funext x
  rw [convolution_eq_swap]
  simp only [mollify, ContinuousLinearMap.lsmul_apply, Complex.real_smul]

/- English proof (translation)
Introduce `n Ω f hΩ hf x₀ hx₀`. Use `ContDiffAt.contDiffWithinAt ?_` and prove the remaining obligations. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.mp hΩ x₀ hx₀`. Use `set r := ε / 4 with hr`. Establish `hr0 : 0 < r` using `by positivity`.

Establish `hsub : closedBall x₀ (3 * r) ⊆ Ω` using `(Metric.closedBall_subset_ball (by linarith)).trans hball`. Use `set g := (closedBall x₀ (3 * r)).indicator f with hg`. Establish `hgi : Integrable g`. Rewrite using `[hg, integrable_indicator_iff measurableSet_closedBall]`. Conclude with `(hf.continuousOn.mono hsub).integrableOn_compact (isCompact_closedBall x₀ (3 * r))`.

Establish `hconv : ContDiff ℝ ∞ (mollify n r g)`. Rewrite using `[mollify_eq_convolution]`. Conclude with `(moll_hasCompactSupport n hr0).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (moll_contDiff n r) hgi.locallyIntegrable`. Establish `heq : f =ᶠ[𝓝 x₀] mollify n r g` using `by filter_upwards [Metric.ball_mem_nhds x₀ hr0] with x hx`. Rewrite `hx` using `[Metric.mem_ball]`.

Establish `hx' : closedBall x r ⊆ Ω`. Use `(Metric.closedBall_subset_closedBall' ?_).trans hsub` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← holo_eq_mollify hr0 (hf.mono hx')]`. Simplify using `only [mollify]`.

Use `congr 1`. Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : y ∈ closedBall x₀ (3 * r)`. Simplify using `[hg, Set.indicator_of_mem hy]`. Establish `h1 : r / 2 < ‖x - y‖`.

Rewrite `hy` using `[Metric.mem_closedBall, not_le]`. Establish `h2` using `dist_triangle y x x₀`. Establish `h3 : dist y x = ‖x - y‖` using `by rw [dist_comm, dist_eq_norm]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `[hg, moll_eq_zero_of_lt hr0 h1]`.

Conclude with `hconv.contDiffAt.congr_of_eventuallyEq heq`.
-/
theorem holoSmooth : HoloSmoothStatement := by
  intro n Ω f hΩ hf x₀ hx₀
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  set r := ε / 4 with hr
  have hr0 : 0 < r := by positivity
  have hsub : closedBall x₀ (3 * r) ⊆ Ω :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  set g := (closedBall x₀ (3 * r)).indicator f with hg
  have hgi : Integrable g := by
    rw [hg, integrable_indicator_iff measurableSet_closedBall]
    exact (hf.continuousOn.mono hsub).integrableOn_compact (isCompact_closedBall x₀ (3 * r))
  have hconv : ContDiff ℝ ∞ (mollify n r g) := by
    rw [mollify_eq_convolution]
    exact (moll_hasCompactSupport n hr0).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (moll_contDiff n r) hgi.locallyIntegrable
  have heq : f =ᶠ[𝓝 x₀] mollify n r g := by
    filter_upwards [Metric.ball_mem_nhds x₀ hr0] with x hx
    rw [Metric.mem_ball] at hx
    have hx' : closedBall x r ⊆ Ω := by
      refine (Metric.closedBall_subset_closedBall' ?_).trans hsub
      linarith
    rw [← holo_eq_mollify hr0 (hf.mono hx')]
    simp only [mollify]
    congr 1
    funext y
    by_cases hy : y ∈ closedBall x₀ (3 * r)
    · simp [hg, Set.indicator_of_mem hy]
    · have h1 : r / 2 < ‖x - y‖ := by
        rw [Metric.mem_closedBall, not_le] at hy
        have h2 := dist_triangle y x x₀
        have h3 : dist y x = ‖x - y‖ := by rw [dist_comm, dist_eq_norm]
        linarith
      simp [hg, moll_eq_zero_of_lt hr0 h1]
  exact hconv.contDiffAt.congr_of_eventuallyEq heq

/- English proof (translation)
Conclude with `holoSmooth n Ω f hΩ hf`.
-/
theorem holo_contDiffOn {n : ℕ} {Ω : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω) :
    ContDiffOn ℝ ∞ f Ω := by
  exact holoSmooth n Ω f hΩ hf

end ReciprocityTheory.L2DbarEstimates.C
