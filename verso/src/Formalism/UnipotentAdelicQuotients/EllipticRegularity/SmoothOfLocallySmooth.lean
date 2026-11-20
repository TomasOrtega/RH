import Formalism.UnipotentAdelicQuotients.EllRegCut

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

/- English proof (translation)
Introduce `d g _ _ ξ`. Rewrite using `[Real.fourier_eq']`. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Use `show g y * eF ξ y = Complex.exp (((-2 * Real.pi * inner ℝ y ξ : ℝ) : ℂ) * Complex.I) • g y`. Rewrite using `[smul_eq_mul, mul_comm (Complex.exp _)]`.

Use `congr 1`. Simplify using `only [eF]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integralFourierChar : FourierPair := by
  intro d g _ _ ξ
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show g y * eF ξ y = Complex.exp (((-2 * Real.pi * inner ℝ y ξ : ℝ) : ℂ) * Complex.I) • g y
  rw [smul_eq_mul, mul_comm (Complex.exp _)]
  congr 1
  simp only [eF]
  congr 1
  push_cast
  ring

/- English proof (translation)
Introduce `d x0 r hr`. Set `f : ContDiffBump x0` to `⟨r / 4, r / 2, by positivity, by linarith⟩`. Use `⟨f, f.contDiff, f.hasCompactSupport, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[f.tsupport_eq]`. Conclude with `closedBall_subset_ball (show r / 2 < r by linarith)`.

Use `filter_upwards [ball_mem_nhds x0 (show (0 : ℝ) < r / 4 by positivity)] with y hy`. Conclude with `f.one_of_mem_closedBall (ball_subset_closedBall hy)`.
-/
theorem existsBump : Bump := by
  intro d x0 r hr
  let f : ContDiffBump x0 := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨f, f.contDiff, f.hasCompactSupport, ?_, ?_⟩
  · rw [f.tsupport_eq]
    exact closedBall_subset_ball (show r / 2 < r by linarith)
  · filter_upwards [ball_mem_nhds x0 (show (0 : ℝ) < r / 4 by positivity)] with y hy
    exact f.one_of_mem_closedBall (ball_subset_closedBall hy)

/- English proof (translation)
Introduce `d U u χ hU hu hχs hχc hχt`. Establish `hχ' : Continuous (fun x => (χ x : ℂ))` using `Complex.continuous_ofReal.comp hχs.continuous`. Establish `hsub : tsupport (cut χ u) ⊆ tsupport χ`. Apply `closure_mono` to reduce the goal to its premises. Introduce `x hx`.

Assume the negation of the conclusion as `h0`. Apply `hx` to reduce the goal to its premises. Establish `h0' : χ x = 0` using `by simpa using h0`. Simplify using `[cut, h0']`. Establish `hcont : ContinuousOn (cut χ u) U` using `hχ'.continuousOn.mul hu`.

Conclude with `⟨hcont.continuous_of_tsupport_subset hU (hsub.trans hχt), IsCompact.of_isClosed_subset hχc (isClosed_tsupport _) hsub⟩`.
-/
theorem cutoffContinuous : CutCont := by
  intro d U u χ hU hu hχs hχc hχt
  have hχ' : Continuous (fun x => (χ x : ℂ)) := Complex.continuous_ofReal.comp hχs.continuous
  have hsub : tsupport (cut χ u) ⊆ tsupport χ := by
    apply closure_mono
    intro x hx
    by_contra h0
    apply hx
    have h0' : χ x = 0 := by simpa using h0
    simp [cut, h0']
  have hcont : ContinuousOn (cut χ u) U := hχ'.continuousOn.mul hu
  exact ⟨hcont.continuous_of_tsupport_subset hU (hsub.trans hχt),
    IsCompact.of_isClosed_subset hχc (isClosed_tsupport _) hsub⟩

/- English proof (translation)
Introduce `d U f _ h x hx`. Take `⟨χ, hχ1, hχf⟩` from `h x hx`. Establish `heq : cut χ f =ᶠ[𝓝 x] f` using `by filter_upwards [hχ1] with y hy`. Simplify using `[cut, hy]`. Conclude with `(hχf.contDiffAt.congr_of_eventuallyEq heq.symm).contDiffWithinAt`.
-/
theorem smoothOfLocallySmooth : LocalGlobal := by
  intro d U f _ h x hx
  obtain ⟨χ, hχ1, hχf⟩ := h x hx
  have heq : cut χ f =ᶠ[𝓝 x] f := by
    filter_upwards [hχ1] with y hy
    simp [cut, hy]
  exact (hχf.contDiffAt.congr_of_eventuallyEq heq.symm).contDiffWithinAt

end ZetaZeros.D.EllReg
