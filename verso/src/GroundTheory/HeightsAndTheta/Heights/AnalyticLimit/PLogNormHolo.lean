import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)

/- English proof (translation)
Introduce `x hx`. Take `⟨j, hj⟩` from `A.cover x`. Establish `hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W` using `⟨(A.chart j).map_source hj, by show (A.chart j).symm (A.chart j x) ∈ W`. Rewrite using `[(A.chart j).left_inv hj]`. Conclude with `hx⟩`.

Establish `h1 : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j x)` using `(hg j _ hmem).continuousAt`. Establish `h2 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) x` using `ContinuousAt.comp h1 ((A.chart j).continuousAt hj)`. Establish `heq : (g ∘ (A.chart j).symm) ∘ A.chart j =ᶠ[nhds x] g` using `by filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz`. Simplify using `[Function.comp, (A.chart j).left_inv hz]`. Conclude with `(h2.congr heq).continuousWithinAt`.
-/
theorem continuousOn_of_holoOn {X : Type} [TopologicalSpace X] {D : ℕ} (A : FinHolAtlas D X)
    {W : Set X} {g : X → ℂ} (hg : A.HoloOn W g) : ContinuousOn g W := by
  intro x hx
  obtain ⟨j, hj⟩ := A.cover x
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by
      show (A.chart j).symm (A.chart j x) ∈ W
      rw [(A.chart j).left_inv hj]; exact hx⟩
  have h1 : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j x) := (hg j _ hmem).continuousAt
  have h2 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) x :=
    ContinuousAt.comp h1 ((A.chart j).continuousAt hj)
  have heq : (g ∘ (A.chart j).symm) ∘ A.chart j =ᶠ[nhds x] g := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
    simp [Function.comp, (A.chart j).left_inv hz]
  exact (h2.congr heq).continuousWithinAt

/- English proof (translation)
Establish `hc : g y ≠ 0` using `hne y hy`. Establish `hcn : 0 < ‖g y‖` using `norm_pos_iff.2 hc`. Establish `hslit : ∀ w ∈ Metric.ball (g y) ‖g y‖, w / g y ∈ Complex.slitPlane`. Introduce `w hw`. Apply `Complex.ball_one_subset_slitPlane` to reduce the goal to its premises.

Rewrite `hw`, the goal using `[Metric.mem_ball, dist_eq_norm]`. Establish `: w / g y - 1 = (w - g y) / g y` using `by field_simp`. Rewrite using `[this, norm_div, div_lt_one hcn]`. Conclude with `hw`. Use `⟨W ∩ g ⁻¹' Metric.ball (g y) ‖g y‖, hgc.isOpen_inter_preimage hW Metric.isOpen_ball, ⟨hy, by simpa using hcn⟩, Set.inter_subset_left, fun z => Complex.log (g z / g y) + (Real.log ‖g y‖ : ℂ), ?_, ?_⟩` and prove the remaining obligations.

Introduce `j v hv`. Establish `ha : AnalyticAt ℂ (g ∘ (A.chart j).symm) v` using `hg j v ⟨hv.1, hv.2.1⟩`. Establish `hs : (g ∘ (A.chart j).symm) v / g y ∈ Complex.slitPlane` using `hslit _ hv.2.2`. Conclude with `((ha.div analyticAt_const hc).clog hs).add analyticAt_const`. Introduce `z hz`.

Establish `hz0 : g z ≠ 0` using `hne z hz.1`. Simplify using `only [Complex.add_re, Complex.log_re, Complex.ofReal_re]`. Rewrite using `[norm_div, Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 hc)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem logNormHolo_of_continuousOn {X : Type} [TopologicalSpace X] {D : ℕ} (A : FinHolAtlas D X)
    {W : Set X} {g : X → ℂ} (hW : IsOpen W) (hg : A.HoloOn W g) (hgc : ContinuousOn g W)
    (hne : ∀ y ∈ W, g y ≠ 0) {y : X} (hy : y ∈ W) : ∃ V : Set X, IsOpen V ∧ y ∈ V ∧
      V ⊆ W ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ z ∈ V, Real.log ‖g z‖ = (G z).re := by
  have hc : g y ≠ 0 := hne y hy
  have hcn : 0 < ‖g y‖ := norm_pos_iff.2 hc

  have hslit : ∀ w ∈ Metric.ball (g y) ‖g y‖, w / g y ∈ Complex.slitPlane := by
    intro w hw
    apply Complex.ball_one_subset_slitPlane
    rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
    have : w / g y - 1 = (w - g y) / g y := by field_simp
    rw [this, norm_div, div_lt_one hcn]
    exact hw
  refine ⟨W ∩ g ⁻¹' Metric.ball (g y) ‖g y‖, hgc.isOpen_inter_preimage hW Metric.isOpen_ball,
    ⟨hy, by simpa using hcn⟩, Set.inter_subset_left,
    fun z => Complex.log (g z / g y) + (Real.log ‖g y‖ : ℂ), ?_, ?_⟩
  · intro j v hv
    have ha : AnalyticAt ℂ (g ∘ (A.chart j).symm) v := hg j v ⟨hv.1, hv.2.1⟩
    have hs : (g ∘ (A.chart j).symm) v / g y ∈ Complex.slitPlane := hslit _ hv.2.2
    exact ((ha.div analyticAt_const hc).clog hs).add analyticAt_const
  · intro z hz
    have hz0 : g z ≠ 0 := hne z hz.1
    simp only [Complex.add_re, Complex.log_re, Complex.ofReal_re]
    rw [norm_div, Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 hc)]
    ring

/- English proof (translation)
Introduce `X _ D A W g hW hg hne y hy`. Conclude with `logNormHolo_of_continuousOn A hW hg ((hCC D A W hW).2 g hg) hne hy`.
-/
theorem LogNormHolo.proof (hCC : ChartCont.Statement) : LogNormHolo.Statement := by
  intro X _ D A W g hW hg hne y hy
  exact logNormHolo_of_continuousOn A hW hg ((hCC D A W hW).2 g hg) hne hy

/- English proof (translation)
Introduce `X _ D A W g hW hg hne y hy`. Conclude with `logNormHolo_of_continuousOn A hW hg (continuousOn_of_holoOn A hg) hne hy`.
-/
theorem LogNormHolo.full : LogNormHolo.Statement := by
  intro X _ D A W g hW hg hne y hy
  exact logNormHolo_of_continuousOn A hW hg (continuousOn_of_holoOn A hg) hne hy

end GroundTheory.Heights₂.Heights.AnalyticLimit
