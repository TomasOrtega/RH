import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalGermIrreducible
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalRiemannExtensionLocal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularLocusIdentity
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVanishNearPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalLocallyIrreducible
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

/- English proof (translation)
Establish `h1` using `hk.continuousWithinAt.mem_closure_image hu`. Establish `h2 : k '' S ⊆ {0}`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `h0 y hy`. Establish `h3` using `closure_mono h2 h1`.

Rewrite `h3` using `[closure_singleton, Set.mem_singleton_iff]`. Then use the resulting hypothesis.
-/
theorem eq_zero_of_mem_closure_of_continuousAt {σ : Type} [Fintype σ] {k : (σ → ℂ) → ℂ}
    {S : Set (σ → ℂ)} {u : σ → ℂ} (hk : ContinuousAt k u) (hu : u ∈ closure S)
    (h0 : ∀ y ∈ S, k y = 0) : k u = 0 := by
  have h1 := hk.continuousWithinAt.mem_closure_image hu
  have h2 : k '' S ⊆ {0} := by
    rintro _ ⟨y, hy, rfl⟩
    exact h0 y hy
  have h3 := closure_mono h2 h1
  rwa [closure_singleton, Set.mem_singleton_iff] at h3

/- English proof (translation)
Introduce `σ _ I w hI hnorm hw`. Use `⟨hw, fun f g hf hg hfg => ?_⟩` and prove the remaining obligations. Use `set X := zeroSetIn I with hX`. Take `⟨h, hhI, hid⟩` from `hreg σ I hI`. Use `set U : Set (σ → ℂ) := {z | AnalyticAt ℂ f z} ∩ {z | AnalyticAt ℂ g z} ∩ {z | ∀ᶠ y in 𝓝 z, y ∈ X → f y * g y = 0} with hUdef`.

Establish `hUo : IsOpen U` using `(isOpen_analyticAt ℂ f).inter (isOpen_analyticAt ℂ g) |>.inter isOpen_setOfPred_eventually_nhds`. Establish `hwU : w ∈ U` using `⟨⟨hf, hg⟩, hfg⟩`. Use `set E : (σ → ℂ) → Prop := fun z => ∀ᶠ y in 𝓝 z, y ∈ X → f y = 0 with hE`. Establish `key : ∀ z ∈ X ∩ U, eval z h ≠ 0 → ∃ V : Set (σ → ℂ), IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧ ((∀ u ∈ X ∩ V, E u) ∨ (∀ u ∈ X ∩ V, ¬ E u ∧ g u = 0))`. Introduce and unpack `z ⟨hzX, hzU⟩ hhz`.

Take `⟨V, hVo, hzV, hVU, hVid⟩` from `hid z hzX hhz U (hUo.mem_nhds hzU)`. Use `⟨V, hVo, hzV, hVU, ?_⟩` and prove the remaining obligations. Establish `hfV : AnalyticOnNhd ℂ f V` using `fun y hy => (hVU hy).1.1`. Establish `hgV : AnalyticOnNhd ℂ g V` using `fun y hy => (hVU hy).1.2`. Distinguish the cases in `hA : ∃ y ∈ X ∩ V, E y`.

Use `left`. Establish `hf0` using `hVid f hfV hA`. Introduce `u hu`. Use `filter_upwards [hVo.mem_nhds hu.2] with y hyV hyX using hf0 y ⟨hyX, hyV⟩`. Use `right push Not at hA`.

Establish `hnz : ¬ E z` using `hA z ⟨hzX, hzV⟩`. Establish `hfr : ∃ᶠ y in 𝓝 z, y ∈ X ∧ f y ≠ 0`. Rewrite `hnz` using `[Filter.not_eventually]`. Use `hnz.mono fun y hy => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`.

Conclude with `hy fun hyX => by_contra fun hne => hc ⟨hyX, hne⟩`. Take `⟨y, ⟨hyX, hfy⟩, hyV⟩` from `(hfr.and_eventually (hVo.mem_nhds hzV)).exists`. Establish `hg0 : ∀ᶠ u in 𝓝 y, u ∈ X → g u = 0` using `by filter_upwards [(hVU hyV).2, (hfV y hyV).continuousAt.eventually_ne hfy] with u hu hfu huX`. Conclude with `(mul_eq_zero.1 (hu huX)).resolve_left hfu`. Establish `hg0V` using `hVid g hgV ⟨y, ⟨hyX, hyV⟩, hg0⟩`.

Conclude with `fun u hu => ⟨hA u hu, hg0V u hu⟩`. Use `set φ : (σ → ℂ) → ℂ := fun z => if E z then 0 else 1 with hφ`. Use `set S := (X ∩ U) \ {z | eval z h = 0} with hS`. Establish `hφhol : HolomorphicOnSubset φ S`. Introduce and unpack `z ⟨hzXU, hhz⟩`.

Take `⟨V, hVo, hzV, -, hcase⟩` from `key z hzXU hhz`. Use `⟨V, hVo, hzV, ?_⟩` and prove the remaining obligations. Break down `hcase with h0 | h1` into its components or cases. Use `⟨fun _ => 0, differentiableOn_const _, fun u hu => ?_⟩` and prove the remaining obligations. Simplify using `only [hφ, if_pos (h0 u ⟨hu.1.1.1, hu.2⟩)]`.

Use `⟨fun _ => 1, differentiableOn_const _, fun u hu => ?_⟩` and prove the remaining obligations. Simplify using `only [hφ, if_neg (h1 u ⟨hu.1.1.1, hu.2⟩).1]`. Establish `hφb : Bornology.IsBounded (φ '' S)`. Use `((Set.finite_singleton (1 : ℂ)).insert 0).isBounded.subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, -, rfl⟩`.

Distinguish the cases in `hz : E z`. Simplify using `[hφ, hz]`. Simplify using `[hφ, hz]`. Take `⟨V, hVo, hwV, hVU, F, hFd, hFeq⟩` from `hext σ I h w U φ hI hnorm hhI hw (hUo.mem_nhds hwU) hφhol hφb`. Use `set N := V ∩ F ⁻¹' Metric.ball (F w) (1 / 2) with hN`.

Establish `hNo : IsOpen N` using `hFd.continuousOn.isOpen_inter_preimage hVo Metric.isOpen_ball`. Establish `hwN : w ∈ N` using `⟨hwV, Metric.mem_ball_self (by norm_num)⟩`. Establish `hdense` using `zeroSetIn_subset_closure_diff hvan I h hI hhI`. Establish `spread : ∀ k : (σ → ℂ) → ℂ, (∀ y ∈ U, ContinuousAt k y) → (∀ y ∈ X ∩ N, eval y h ≠ 0 → k y = 0) → ∀ᶠ u in 𝓝 w, u ∈ X → k u = 0`. Introduce `k hk h0`.

Use `filter_upwards [hNo.mem_nhds hwN] with u huN huX`. Establish `hcl : u ∈ closure (N ∩ (X \ {z | eval z h = 0}))` using `hNo.inter_closure ⟨huN, hdense huX⟩`. Conclude with `eq_zero_of_mem_closure_of_continuousAt (hk u (hVU huN.1)) hcl fun y hy => h0 y ⟨hy.2.1, hy.1⟩ hy.2.2`. Establish `hφN : ∀ y ∈ X ∩ N, eval y h ≠ 0 → ‖φ y - F w‖ < 1 / 2`. Introduce and unpack `y ⟨hyX, hyV, hyF⟩ hhy`.

Rewrite using `[← hFeq ⟨⟨hyX, hyV⟩, hhy⟩]`. Simplify `hyF` using `[dist_eq_norm]`. Distinguish the cases in `hc : ‖F w‖ < 1 / 2`. Use `left`. Use `spread f (fun y hy => hy.1.1.continuousAt) fun y hy hhy => ?_` and prove the remaining obligations.

Establish `hEy : E y`. Assume the negation of the conclusion as `hnE`. Establish `h1` using `hφN y hy hhy`. Simplify using `only [hφ, if_neg hnE] at h1`. Establish `: ‖(1 : ℂ)‖ < 1`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `at this`. Conclude with `hEy.self_of_nhds hy.1`. Use `right`. Use `spread g (fun y hy => hy.1.2.continuousAt) fun y hy hhy => ?_` and prove the remaining obligations.

Establish `hnE : ¬ E y`. Introduce `hEy`. Establish `h1` using `hφN y hy hhy`. Simplify using `only [hφ, if_pos hEy, zero_sub, norm_neg] at h1`. Conclude with `hc h1`.

Take `⟨V', -, hyV', -, hcase⟩` from `key y ⟨hy.1, hVU hy.2.1⟩ hhy`. Break down `hcase with h0 | h1` into its components or cases. Conclude with `absurd (h0 y ⟨hy.1, hyV'⟩) hnE`. Conclude with `(h1 y ⟨hy.1, hyV'⟩).2`.
-/
theorem NormalGermIrreducible.proof (hreg : RegularLocusIdentity.Statement)
    (hext : NormalRiemannExtensionLocal.Statement) (hvan : VanishNearPoint.Statement) :
    NormalGermIrreducible.Statement := by
  classical
  intro σ _ I w hI hnorm hw
  refine ⟨hw, fun f g hf hg hfg => ?_⟩
  set X := zeroSetIn I with hX
  obtain ⟨h, hhI, hid⟩ := hreg σ I hI

  set U : Set (σ → ℂ) := {z | AnalyticAt ℂ f z} ∩ {z | AnalyticAt ℂ g z} ∩
    {z | ∀ᶠ y in 𝓝 z, y ∈ X → f y * g y = 0} with hUdef
  have hUo : IsOpen U :=
    (isOpen_analyticAt ℂ f).inter (isOpen_analyticAt ℂ g) |>.inter isOpen_setOfPred_eventually_nhds
  have hwU : w ∈ U := ⟨⟨hf, hg⟩, hfg⟩

  set E : (σ → ℂ) → Prop := fun z => ∀ᶠ y in 𝓝 z, y ∈ X → f y = 0 with hE

  have key : ∀ z ∈ X ∩ U, eval z h ≠ 0 → ∃ V : Set (σ → ℂ), IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      ((∀ u ∈ X ∩ V, E u) ∨ (∀ u ∈ X ∩ V, ¬ E u ∧ g u = 0)) := by
    rintro z ⟨hzX, hzU⟩ hhz
    obtain ⟨V, hVo, hzV, hVU, hVid⟩ := hid z hzX hhz U (hUo.mem_nhds hzU)
    refine ⟨V, hVo, hzV, hVU, ?_⟩
    have hfV : AnalyticOnNhd ℂ f V := fun y hy => (hVU hy).1.1
    have hgV : AnalyticOnNhd ℂ g V := fun y hy => (hVU hy).1.2
    by_cases hA : ∃ y ∈ X ∩ V, E y
    · left
      have hf0 := hVid f hfV hA
      intro u hu
      filter_upwards [hVo.mem_nhds hu.2] with y hyV hyX using hf0 y ⟨hyX, hyV⟩
    · right
      push Not at hA
      have hnz : ¬ E z := hA z ⟨hzX, hzV⟩
      have hfr : ∃ᶠ y in 𝓝 z, y ∈ X ∧ f y ≠ 0 := by
        rw [Filter.not_eventually] at hnz
        refine hnz.mono fun y hy => ?_
        by_contra hc
        exact hy fun hyX => by_contra fun hne => hc ⟨hyX, hne⟩
      obtain ⟨y, ⟨hyX, hfy⟩, hyV⟩ := (hfr.and_eventually (hVo.mem_nhds hzV)).exists
      have hg0 : ∀ᶠ u in 𝓝 y, u ∈ X → g u = 0 := by
        filter_upwards [(hVU hyV).2, (hfV y hyV).continuousAt.eventually_ne hfy] with u hu hfu huX
        exact (mul_eq_zero.1 (hu huX)).resolve_left hfu
      have hg0V := hVid g hgV ⟨y, ⟨hyX, hyV⟩, hg0⟩
      exact fun u hu => ⟨hA u hu, hg0V u hu⟩

  set φ : (σ → ℂ) → ℂ := fun z => if E z then 0 else 1 with hφ
  set S := (X ∩ U) \ {z | eval z h = 0} with hS
  have hφhol : HolomorphicOnSubset φ S := by
    rintro z ⟨hzXU, hhz⟩
    obtain ⟨V, hVo, hzV, -, hcase⟩ := key z hzXU hhz
    refine ⟨V, hVo, hzV, ?_⟩
    rcases hcase with h0 | h1
    · refine ⟨fun _ => 0, differentiableOn_const _, fun u hu => ?_⟩
      simp only [hφ, if_pos (h0 u ⟨hu.1.1.1, hu.2⟩)]
    · refine ⟨fun _ => 1, differentiableOn_const _, fun u hu => ?_⟩
      simp only [hφ, if_neg (h1 u ⟨hu.1.1.1, hu.2⟩).1]
  have hφb : Bornology.IsBounded (φ '' S) := by
    refine ((Set.finite_singleton (1 : ℂ)).insert 0).isBounded.subset ?_
    rintro _ ⟨z, -, rfl⟩
    by_cases hz : E z
    · simp [hφ, hz]
    · simp [hφ, hz]
  obtain ⟨V, hVo, hwV, hVU, F, hFd, hFeq⟩ :=
    hext σ I h w U φ hI hnorm hhI hw (hUo.mem_nhds hwU) hφhol hφb

  set N := V ∩ F ⁻¹' Metric.ball (F w) (1 / 2) with hN
  have hNo : IsOpen N := hFd.continuousOn.isOpen_inter_preimage hVo Metric.isOpen_ball
  have hwN : w ∈ N := ⟨hwV, Metric.mem_ball_self (by norm_num)⟩
  have hdense := zeroSetIn_subset_closure_diff hvan I h hI hhI

  have spread : ∀ k : (σ → ℂ) → ℂ, (∀ y ∈ U, ContinuousAt k y) →
      (∀ y ∈ X ∩ N, eval y h ≠ 0 → k y = 0) → ∀ᶠ u in 𝓝 w, u ∈ X → k u = 0 := by
    intro k hk h0
    filter_upwards [hNo.mem_nhds hwN] with u huN huX
    have hcl : u ∈ closure (N ∩ (X \ {z | eval z h = 0})) := hNo.inter_closure ⟨huN, hdense huX⟩
    exact eq_zero_of_mem_closure_of_continuousAt (hk u (hVU huN.1)) hcl
      fun y hy => h0 y ⟨hy.2.1, hy.1⟩ hy.2.2
  have hφN : ∀ y ∈ X ∩ N, eval y h ≠ 0 → ‖φ y - F w‖ < 1 / 2 := by
    rintro y ⟨hyX, hyV, hyF⟩ hhy
    rw [← hFeq ⟨⟨hyX, hyV⟩, hhy⟩]
    simpa [dist_eq_norm] using hyF
  by_cases hc : ‖F w‖ < 1 / 2
  · left
    refine spread f (fun y hy => hy.1.1.continuousAt) fun y hy hhy => ?_
    have hEy : E y := by
      by_contra hnE
      have h1 := hφN y hy hhy
      simp only [hφ, if_neg hnE] at h1
      have : ‖(1 : ℂ)‖ < 1 := by
        calc ‖(1 : ℂ)‖ = ‖(1 - F w) + F w‖ := by ring_nf
          _ ≤ ‖1 - F w‖ + ‖F w‖ := norm_add_le _ _
          _ < 1 / 2 + 1 / 2 := add_lt_add h1 hc
          _ = 1 := by norm_num
      simp at this
    exact hEy.self_of_nhds hy.1
  · right
    refine spread g (fun y hy => hy.1.2.continuousAt) fun y hy hhy => ?_
    have hnE : ¬ E y := by
      intro hEy
      have h1 := hφN y hy hhy
      simp only [hφ, if_pos hEy, zero_sub, norm_neg] at h1
      exact hc h1
    obtain ⟨V', -, hyV', -, hcase⟩ := key y ⟨hy.1, hVU hy.2.1⟩ hhy
    rcases hcase with h0 | h1
    · exact absurd (h0 y ⟨hy.1, hyV'⟩) hnE
    · exact (h1 y ⟨hy.1, hyV'⟩).2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
