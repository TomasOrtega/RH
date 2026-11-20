import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiAnalyticNormality
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

noncomputable section

def HolGermsDomain.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ), IsDomain (holGerms w)

/- English proof (translation)
Take `⟨r₁, hr₁, hf'⟩` from `hf.exists_ball_analyticOnNhd`. Take `⟨r₂, hr₂, hg'⟩` from `hg.exists_ball_analyticOnNhd`. Take `⟨r₃, hr₃, hfg'⟩` from `Metric.eventually_nhds_iff_ball.1 hfg`. Establish `hr : 0 < min r₁ (min r₂ r₃)` using `lt_min hr₁ (lt_min hr₂ hr₃)`. Establish `hU1 : ball w (min r₁ (min r₂ r₃)) ⊆ ball w r₁` using `ball_subset_ball (min_le_left _ _)`.

Establish `hU2 : ball w (min r₁ (min r₂ r₃)) ⊆ ball w r₂` using `ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))`. Establish `hU3 : ball w (min r₁ (min r₂ r₃)) ⊆ ball w r₃` using `ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))`. Distinguish the cases in `h : ∀ z ∈ ball w (min r₁ (min r₂ r₃)), f z = 0`. Use `left filter_upwards [ball_mem_nhds w hr] with x hx`. Conclude with `h x hx`.

Use `right push Not at h`. Take `⟨z, hz, hfz⟩` from `h`. Establish `hgz : g =ᶠ[𝓝 z] 0`. Establish `h1 : ∀ᶠ x in 𝓝 z, f x ≠ 0` using `(hf' z (hU1 hz)).continuousAt.eventually_ne hfz`. Establish `h2 : ∀ᶠ x in 𝓝 z, x ∈ ball w (min r₁ (min r₂ r₃))` using `isOpen_ball.mem_nhds hz`.

Use `filter_upwards [h1, h2] with x hx1 hx2`. Establish `h3` using `hfg' x (hU3 hx2)`. Simplify `h3` using `[hx1]`. Establish `hEq` using `(hg'.mono hU2).eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball w _).isPreconnected hz hgz`. Use `filter_upwards [ball_mem_nhds w hr] with x hx`.

Simplify using `using hEq hx`.
-/
theorem eventually_zero_or_of_mul_eventually_zero {σ : Type} [Fintype σ] {w : σ → ℂ}
    {f g : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w) (hg : AnalyticAt ℂ g w)
    (hfg : ∀ᶠ z in 𝓝 w, f z * g z = 0) :
    (∀ᶠ z in 𝓝 w, f z = 0) ∨ ∀ᶠ z in 𝓝 w, g z = 0 := by
  obtain ⟨r₁, hr₁, hf'⟩ := hf.exists_ball_analyticOnNhd
  obtain ⟨r₂, hr₂, hg'⟩ := hg.exists_ball_analyticOnNhd
  obtain ⟨r₃, hr₃, hfg'⟩ := Metric.eventually_nhds_iff_ball.1 hfg
  have hr : 0 < min r₁ (min r₂ r₃) := lt_min hr₁ (lt_min hr₂ hr₃)
  have hU1 : ball w (min r₁ (min r₂ r₃)) ⊆ ball w r₁ := ball_subset_ball (min_le_left _ _)
  have hU2 : ball w (min r₁ (min r₂ r₃)) ⊆ ball w r₂ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hU3 : ball w (min r₁ (min r₂ r₃)) ⊆ ball w r₃ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  by_cases h : ∀ z ∈ ball w (min r₁ (min r₂ r₃)), f z = 0
  · left
    filter_upwards [ball_mem_nhds w hr] with x hx
    exact h x hx
  · right
    push Not at h
    obtain ⟨z, hz, hfz⟩ := h
    have hgz : g =ᶠ[𝓝 z] 0 := by
      have h1 : ∀ᶠ x in 𝓝 z, f x ≠ 0 := (hf' z (hU1 hz)).continuousAt.eventually_ne hfz
      have h2 : ∀ᶠ x in 𝓝 z, x ∈ ball w (min r₁ (min r₂ r₃)) := isOpen_ball.mem_nhds hz
      filter_upwards [h1, h2] with x hx1 hx2
      have h3 := hfg' x (hU3 hx2)
      simpa [hx1] using h3
    have hEq := (hg'.mono hU2).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball w _).isPreconnected hz hgz
    filter_upwards [ball_mem_nhds w hr] with x hx
    simpa using hEq hx

/- English proof (translation)
Introduce `σ _ w`. Establish `: NoZeroDivisors (holGerms w)`. Use `⟨fun {a b} hab => ?_⟩` and prove the remaining obligations. Take `⟨f, hf, hfa⟩` from `a.2`. Take `⟨g, hg, hgb⟩` from `b.2`.

Establish `h0 : ((f * g : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)`. Rewrite using `[Germ.coe_mul, hfa, hgb]`. Conclude with `congrArg Subtype.val hab`. Establish `h1 : ∀ᶠ z in 𝓝 w, f z * g z = 0` using `(Germ.coe_eq.1 h0).mono fun z hz => by simpa using hz`. Break down `eventually_zero_or_of_mul_eventually_zero hf hg h1 with h | h` into its components or cases.

Use `left`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(a : Germ (𝓝 w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)`. Rewrite using `[← hfa]`. Conclude with `Germ.coe_eq.2 (h.mono fun z hz => by simpa using hz)`.

Use `right`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(b : Germ (𝓝 w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)`. Rewrite using `[← hgb]`. Conclude with `Germ.coe_eq.2 (h.mono fun z hz => by simpa using hz)`.

Conclude with `NoZeroDivisors.to_isDomain _`.
-/
theorem HolGermsDomain.proof : HolGermsDomain.Statement := by
  intro σ _ w
  have : NoZeroDivisors (holGerms w) := by
    refine ⟨fun {a b} hab => ?_⟩
    obtain ⟨f, hf, hfa⟩ := a.2
    obtain ⟨g, hg, hgb⟩ := b.2
    have h0 : ((f * g : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := by
      rw [Germ.coe_mul, hfa, hgb]
      exact congrArg Subtype.val hab
    have h1 : ∀ᶠ z in 𝓝 w, f z * g z = 0 := (Germ.coe_eq.1 h0).mono fun z hz => by simpa using hz
    rcases eventually_zero_or_of_mul_eventually_zero hf hg h1 with h | h
    · left
      apply Subtype.ext
      change (a : Germ (𝓝 w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)
      rw [← hfa]
      exact Germ.coe_eq.2 (h.mono fun z hz => by simpa using hz)
    · right
      apply Subtype.ext
      change (b : Germ (𝓝 w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)
      rw [← hgb]
      exact Germ.coe_eq.2 (h.mono fun z hz => by simpa using hz)
  exact NoZeroDivisors.to_isDomain _

instance holGerms_isDomain {σ : Type} [Fintype σ] (w : σ → ℂ) : IsDomain (holGerms w) :=
  HolGermsDomain.proof σ w

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
