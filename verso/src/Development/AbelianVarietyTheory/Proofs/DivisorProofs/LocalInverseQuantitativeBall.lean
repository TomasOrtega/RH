import Mathlib
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Establish `hUn : U ∈ nhds v₀` using `hU.mem_nhds hv₀`. Establish `hcd : ContDiffAt ℝ 1 Ψ v₀` using `hΨ.contDiffAt hUn`. Establish `hs : HasStrictFDerivAt Ψ (fderiv ℝ Ψ v₀) v₀` using `hcd.hasStrictFDerivAt one_ne_zero`. Set `e : ReciprocityTheory.L2DbarEstimates.V d ≃L[ℝ] ReciprocityTheory.L2DbarEstimates.V d` to `(LinearEquiv.ofBijective ((fderiv ℝ Ψ v₀ : ReciprocityTheory.L2DbarEstimates.V d →L[ℝ] ReciprocityTheory.L2DbarEstimates.V d) : ReciprocityTheory.L2DbarEstimates.V d →ₗ[ℝ] ReciprocityTheory.L2DbarEstimates.V d) hbij).toContinuousLinearEquiv`. Establish `he : (e : ReciprocityTheory.L2DbarEstimates.V d →L[ℝ] ReciprocityTheory.L2DbarEstimates.V d) = fderiv ℝ Ψ v₀`.

Use extensionality with `x`. Both sides reduce to the same expression. Establish `hs' : HasStrictFDerivAt Ψ (e : ReciprocityTheory.L2DbarEstimates.V d →L[ℝ] ReciprocityTheory.L2DbarEstimates.V d) v₀`. Rewrite using `[he]`. Conclude with `hs`.

Use `set P := hs'.toOpenPartialHomeomorph Ψ with hP`. Establish `hsrc : P.source ∈ nhds v₀` using `P.open_source.mem_nhds (hs'.mem_toOpenPartialHomeomorph_source)`. Establish `hinj : Set.InjOn Ψ P.source`. Use `P.injOn` as an intermediate fact. Simplify `this` using `[hP, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]`.

Establish `hcont : ContinuousOn (fderiv ℝ Ψ) U` using `hΨ.continuousOn_fderiv_of_isOpen hU le_rfl`. Establish `hca : ContinuousAt (fderiv ℝ Ψ) v₀` using `hcont.continuousAt hUn`. Establish `hdet0 : (fderiv ℝ Ψ v₀).det ≠ 0`. Use `(LinearEquiv.ofBijective ((fderiv ℝ Ψ v₀ : ReciprocityTheory.L2DbarEstimates.V d →L[ℝ] ReciprocityTheory.L2DbarEstimates.V d) : ReciprocityTheory.L2DbarEstimates.V d →ₗ[ℝ] ReciprocityTheory.L2DbarEstimates.V d) hbij).isUnit_det'` as an intermediate fact. Conclude with `this.ne_zero`.

Use `set J : ℝ := |(fderiv ℝ Ψ v₀).det| / 2 with hJ`. Establish `hJpos : 0 < J` using `by positivity`. Establish `hdc : ContinuousAt (fun v => |(fderiv ℝ Ψ v).det|) v₀` using `(continuous_abs.comp ContinuousLinearMap.continuous_det).continuousAt.comp hca`. Establish `ev1 : ∀ᶠ v in nhds v₀, J < |(fderiv ℝ Ψ v).det|` using `hdc.eventually (lt_mem_nhds (by rw [hJ]; linarith [abs_pos.mpr hdet0]))`. Establish `hnc : ContinuousAt (fun v => ‖fderiv ℝ Ψ v‖) v₀` using `continuous_norm.continuousAt.comp hca`.

Establish `ev2 : ∀ᶠ v in nhds v₀, ‖fderiv ℝ Ψ v‖ < ‖fderiv ℝ Ψ v₀‖ + 1` using `hnc.eventually (gt_mem_nhds (by linarith))`. Establish `ev : ∀ᶠ v in nhds v₀, (v ∈ U ∧ v ∈ P.source) ∧ (J < |(fderiv ℝ Ψ v).det| ∧ ‖fderiv ℝ Ψ v‖ < ‖fderiv ℝ Ψ v₀‖ + 1)` using `(Filter.Eventually.and hUn hsrc).and (ev1.and ev2)`. Take `⟨r, hr, hball⟩` from `Metric.eventually_nhds_iff_ball.mp ev`. Use `⟨r, J, ‖fderiv ℝ Ψ v₀‖ + 1, hr, hJpos, by positivity, fun v hv => (hball v hv).1.1, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hinj.mono (fun v hv => (hball v hv).1.2)`.

Introduce `v hv`. Conclude with `⟨(hball v hv).2.1.le, (hball v hv).2.2.le⟩`.
-/
theorem contDiffOn_one_injOn_ball_det_norm_bounds {d : ℕ} (U : Set (ReciprocityTheory.L2DbarEstimates.V d)) (v₀ : ReciprocityTheory.L2DbarEstimates.V d)
    (Ψ : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d) (hU : IsOpen U) (hv₀ : v₀ ∈ U)
    (hΨ : ContDiffOn ℝ 1 Ψ U) (hbij : Function.Bijective (fderiv ℝ Ψ v₀)) :
    ∃ r J L : ℝ, 0 < r ∧ 0 < J ∧ 0 ≤ L ∧ Metric.ball v₀ r ⊆ U ∧ Set.InjOn Ψ (Metric.ball v₀ r) ∧
      ∀ v ∈ Metric.ball v₀ r, J ≤ |(fderiv ℝ Ψ v).det| ∧ ‖fderiv ℝ Ψ v‖ ≤ L := by
  have hUn : U ∈ nhds v₀ := hU.mem_nhds hv₀
  have hcd : ContDiffAt ℝ 1 Ψ v₀ := hΨ.contDiffAt hUn
  have hs : HasStrictFDerivAt Ψ (fderiv ℝ Ψ v₀) v₀ := hcd.hasStrictFDerivAt one_ne_zero
  let e : ReciprocityTheory.L2DbarEstimates.V d ≃L[ℝ] ReciprocityTheory.L2DbarEstimates.V d :=
    (LinearEquiv.ofBijective ((fderiv ℝ Ψ v₀ : ReciprocityTheory.L2DbarEstimates.V d →L[ℝ] ReciprocityTheory.L2DbarEstimates.V d) :
      ReciprocityTheory.L2DbarEstimates.V d →ₗ[ℝ] ReciprocityTheory.L2DbarEstimates.V d) hbij).toContinuousLinearEquiv
  have he : (e : ReciprocityTheory.L2DbarEstimates.V d →L[ℝ] ReciprocityTheory.L2DbarEstimates.V d) = fderiv ℝ Ψ v₀ := by
    ext x; rfl
  have hs' : HasStrictFDerivAt Ψ (e : ReciprocityTheory.L2DbarEstimates.V d →L[ℝ] ReciprocityTheory.L2DbarEstimates.V d) v₀ := by
    rw [he]; exact hs
  set P := hs'.toOpenPartialHomeomorph Ψ with hP
  have hsrc : P.source ∈ nhds v₀ :=
    P.open_source.mem_nhds (hs'.mem_toOpenPartialHomeomorph_source)
  have hinj : Set.InjOn Ψ P.source := by
    have := P.injOn
    simpa [hP, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using this
  have hcont : ContinuousOn (fderiv ℝ Ψ) U := hΨ.continuousOn_fderiv_of_isOpen hU le_rfl
  have hca : ContinuousAt (fderiv ℝ Ψ) v₀ := hcont.continuousAt hUn
  have hdet0 : (fderiv ℝ Ψ v₀).det ≠ 0 := by
    have := (LinearEquiv.ofBijective ((fderiv ℝ Ψ v₀ : ReciprocityTheory.L2DbarEstimates.V d →L[ℝ] ReciprocityTheory.L2DbarEstimates.V d) :
      ReciprocityTheory.L2DbarEstimates.V d →ₗ[ℝ] ReciprocityTheory.L2DbarEstimates.V d) hbij).isUnit_det'
    exact this.ne_zero
  set J : ℝ := |(fderiv ℝ Ψ v₀).det| / 2 with hJ
  have hJpos : 0 < J := by positivity
  have hdc : ContinuousAt (fun v => |(fderiv ℝ Ψ v).det|) v₀ :=
    (continuous_abs.comp ContinuousLinearMap.continuous_det).continuousAt.comp hca
  have ev1 : ∀ᶠ v in nhds v₀, J < |(fderiv ℝ Ψ v).det| :=
    hdc.eventually (lt_mem_nhds (by rw [hJ]; linarith [abs_pos.mpr hdet0]))
  have hnc : ContinuousAt (fun v => ‖fderiv ℝ Ψ v‖) v₀ := continuous_norm.continuousAt.comp hca
  have ev2 : ∀ᶠ v in nhds v₀, ‖fderiv ℝ Ψ v‖ < ‖fderiv ℝ Ψ v₀‖ + 1 :=
    hnc.eventually (gt_mem_nhds (by linarith))
  have ev : ∀ᶠ v in nhds v₀, (v ∈ U ∧ v ∈ P.source) ∧ (J < |(fderiv ℝ Ψ v).det| ∧
      ‖fderiv ℝ Ψ v‖ < ‖fderiv ℝ Ψ v₀‖ + 1) :=
    (Filter.Eventually.and hUn hsrc).and (ev1.and ev2)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp ev
  refine ⟨r, J, ‖fderiv ℝ Ψ v₀‖ + 1, hr, hJpos, by positivity, fun v hv => (hball v hv).1.1, ?_, ?_⟩
  · exact hinj.mono (fun v hv => (hball v hv).1.2)
  · intro v hv
    exact ⟨(hball v hv).2.1.le, (hball v hv).2.2.le⟩

end GlobalTheory
