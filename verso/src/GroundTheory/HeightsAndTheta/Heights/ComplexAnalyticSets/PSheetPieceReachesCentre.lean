import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetPieceReachesCentre
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PManifoldZerosComplementConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

/- English proof (translation)
Introduce `σ _ X w B d A D δ N U V hpar hU hV hcover hdisj hne`. Take `⟨-, hwXB, hD, hDc, hmaps, hprop, hcentre, hδ, ⟨y₁, hy₁D, hy₁⟩, -, hchart, -⟩` from `hpar`. Use `set T : Set (σ → ℂ) := {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ U with hTdef`. Establish `key : ∀ y ∈ D, y ∈ closure (A '' T) → ∃ x ∈ closure T, x ∈ X ∩ B ∧ A x = y`. Introduce `y hyD hy`.

Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.mp hD y hyD`. Establish `hKD : Metric.closedBall y (ε / 2) ⊆ D` using `(Metric.closedBall_subset_ball (half_lt_self hε)).trans hball`. Establish `hP` using `hprop _ hKD (isCompact_closedBall y (ε / 2))`. Establish `hQsub : closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2)) ⊆ {x | x ∈ X ∩ B ∧ A x ∈ Metric.closedBall y (ε / 2)}` using `closure_minimal (fun x hx => ⟨hx.1.1.1, hx.2⟩) hP.isClosed`. Establish `hQ : IsCompact (closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2)))` using `hP.of_isClosed_subset isClosed_closure hQsub`.

Establish `hAQ : IsClosed (A '' closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2)))` using `(hQ.image A.continuous).isClosed`. Establish `hyK : y ∈ closure (A '' (T ∩ A ⁻¹' Metric.closedBall y (ε / 2)))`. Rewrite `hy`, the goal using `[mem_closure_iff_nhds]`. Introduce `t ht`. Take `⟨z, ⟨hzt, hzK⟩, x, hxT, rfl⟩` from `hy (t ∩ Metric.closedBall y (ε / 2)) (Filter.inter_mem ht (Metric.closedBall_mem_nhds y (half_pos hε)))`.

Conclude with `⟨A x, hzt, x, ⟨hxT, hzK⟩, rfl⟩`. Take `⟨x, hxQ, rfl⟩` from `closure_minimal (Set.image_mono subset_closure) hAQ hyK`. Conclude with `⟨x, closure_mono Set.inter_subset_left hxQ, (hQsub hxQ).1, rfl⟩`. Establish `hopen : IsOpen (A '' T)`. Rewrite using `[isOpen_iff_mem_nhds]`.

Introduce and unpack `_ ⟨x, ⟨⟨hxXB, hδx⟩, hxU⟩, rfl⟩`. Take `⟨O, V', g, hO, hV', hxV', hg, hAg, hXBV⟩` from `hchart x hxXB hδx`. Take `⟨y₀, hy₀O, hgy₀⟩ : x ∈ g '' O` from `hXBV ▸ ⟨hxXB, hxV'⟩`. Establish `hAx : A x = y₀` using `by rw [← hgy₀, hAg y₀ hy₀O]`. Substitute `hAx` using the available equality.

Establish `h1 : g ⁻¹' (U ∩ V') ∈ 𝓝 (A x)` using `(hg (A x) hy₀O).continuousAt.preimage_mem_nhds (by rw [hgy₀]; exact (hU.inter hV').mem_nhds ⟨hxU, hxV'⟩)`. Establish `h2 : δ ⁻¹' {0}ᶜ ∈ 𝓝 (A x)` using `(hδ (A x) (hmaps hxXB)).continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hδx)`. Use `filter_upwards [h1, h2, hO.mem_nhds hy₀O] with y hy1 hy2 hy3`. Establish `hgy : g y ∈ X ∩ B ∩ V'` using `hXBV ▸ ⟨y, hy3, rfl⟩`. Use `⟨g y, ⟨⟨hgy.1, ?_⟩, hy1.1⟩, hAg y hy3⟩` and prove the remaining obligations.

Rewrite using `[hAg y hy3]`. Conclude with `hy2`. Establish `hreg : ∀ y ∈ D, IsRegularPointOf D y` using `fun y hy => ⟨hy, d, ContinuousLinearMap.id ℂ _, D, D, id, hD, hD, hy, fun _ _ => analyticAt_id, fun _ _ => rfl, by rw [Set.inter_self, Set.image_id]⟩`. Establish `hE : IsPreconnected (D \ {z | δ z = 0})` using `ManifoldZerosComplementConnected.proof (Fin d) D δ hDc hreg hδ ⟨y₁, hy₁D, hy₁⟩`. Establish `hEsub : D \ {z | δ z = 0} ⊆ A '' T`.

Use `hE.subset_of_closure_inter_subset hopen ?_ ?_` and prove the remaining obligations. Take `⟨x₀, hx₀S, hx₀U⟩` from `hne`. Conclude with `⟨A x₀, ⟨hmaps hx₀S.1, hx₀S.2⟩, x₀, ⟨hx₀S, hx₀U⟩, rfl⟩`. Introduce and unpack `y ⟨hy, hyD, hyδ⟩`. Take `⟨x, hxcl, hxXB, rfl⟩` from `key y hyD hy`.

Establish `hxS : x ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0}` using `⟨hxXB, hyδ⟩`. Break down `hcover hxS with hxU | hxV` into its components or cases. Conclude with `⟨x, ⟨hxS, hxU⟩, rfl⟩`. It suffices to derive a contradiction. Take `⟨z, hzV, hzS, hzU⟩` from `mem_closure_iff.mp hxcl V hV hxV`.

Establish `hz : z ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V)` using `⟨hzS, hzU, hzV⟩`. Rewrite `hz` using `[hdisj]`. Conclude with `hz`. Establish `hwD : A w ∈ D` using `hmaps hwXB`. Establish `hwE : A w ∈ closure (D \ {z | δ z = 0})`.

Assume the negation of the conclusion as `hw`. Rewrite `hw` using `[mem_closure_iff_nhds]`. Use `push Not at hw`. Take `⟨t, ht, hte⟩` from `hw`. Establish `hzero : δ =ᶠ[𝓝 (A w)] 0` using `by filter_upwards [ht, hD.mem_nhds hwD] with y hyt hyD`.

Assume the negation of the conclusion as `hy`. Conclude with `(Set.not_nonempty_iff_eq_empty.mpr hte) ⟨y, hyt, hyD, hy⟩`. Conclude with `hy₁ (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc hwD hzero hy₁D)`. Take `⟨x, hxcl, hxXB, hAx⟩` from `key (A w) hwD (closure_mono hEsub hwE)`. Rewrite using `[← hcentre x hxXB hAx]`.

Conclude with `hxcl`.
-/
theorem SheetPieceReachesCentre.proof : SheetPieceReachesCentre.Statement := by
  intro σ _ X w B d A D δ N U V hpar hU hV hcover hdisj hne
  obtain ⟨-, hwXB, hD, hDc, hmaps, hprop, hcentre, hδ, ⟨y₁, hy₁D, hy₁⟩, -, hchart, -⟩ := hpar
  set T : Set (σ → ℂ) := {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ U with hTdef

  have key : ∀ y ∈ D, y ∈ closure (A '' T) → ∃ x ∈ closure T, x ∈ X ∩ B ∧ A x = y := by
    intro y hyD hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD y hyD
    have hKD : Metric.closedBall y (ε / 2) ⊆ D :=
      (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
    have hP := hprop _ hKD (isCompact_closedBall y (ε / 2))
    have hQsub : closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2)) ⊆
        {x | x ∈ X ∩ B ∧ A x ∈ Metric.closedBall y (ε / 2)} :=
      closure_minimal (fun x hx => ⟨hx.1.1.1, hx.2⟩) hP.isClosed
    have hQ : IsCompact (closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2))) :=
      hP.of_isClosed_subset isClosed_closure hQsub
    have hAQ : IsClosed (A '' closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2))) :=
      (hQ.image A.continuous).isClosed
    have hyK : y ∈ closure (A '' (T ∩ A ⁻¹' Metric.closedBall y (ε / 2))) := by
      rw [mem_closure_iff_nhds] at hy ⊢
      intro t ht
      obtain ⟨z, ⟨hzt, hzK⟩, x, hxT, rfl⟩ :=
        hy (t ∩ Metric.closedBall y (ε / 2)) (Filter.inter_mem ht (Metric.closedBall_mem_nhds y (half_pos hε)))
      exact ⟨A x, hzt, x, ⟨hxT, hzK⟩, rfl⟩
    obtain ⟨x, hxQ, rfl⟩ := closure_minimal (Set.image_mono subset_closure) hAQ hyK
    exact ⟨x, closure_mono Set.inter_subset_left hxQ, (hQsub hxQ).1, rfl⟩

  have hopen : IsOpen (A '' T) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, ⟨⟨hxXB, hδx⟩, hxU⟩, rfl⟩
    obtain ⟨O, V', g, hO, hV', hxV', hg, hAg, hXBV⟩ := hchart x hxXB hδx
    obtain ⟨y₀, hy₀O, hgy₀⟩ : x ∈ g '' O := hXBV ▸ ⟨hxXB, hxV'⟩
    have hAx : A x = y₀ := by rw [← hgy₀, hAg y₀ hy₀O]
    subst hAx
    have h1 : g ⁻¹' (U ∩ V') ∈ 𝓝 (A x) :=
      (hg (A x) hy₀O).continuousAt.preimage_mem_nhds (by rw [hgy₀]; exact (hU.inter hV').mem_nhds ⟨hxU, hxV'⟩)
    have h2 : δ ⁻¹' {0}ᶜ ∈ 𝓝 (A x) :=
      (hδ (A x) (hmaps hxXB)).continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hδx)
    filter_upwards [h1, h2, hO.mem_nhds hy₀O] with y hy1 hy2 hy3
    have hgy : g y ∈ X ∩ B ∩ V' := hXBV ▸ ⟨y, hy3, rfl⟩
    refine ⟨g y, ⟨⟨hgy.1, ?_⟩, hy1.1⟩, hAg y hy3⟩
    rw [hAg y hy3]
    exact hy2

  have hreg : ∀ y ∈ D, IsRegularPointOf D y := fun y hy =>
    ⟨hy, d, ContinuousLinearMap.id ℂ _, D, D, id, hD, hD, hy, fun _ _ => analyticAt_id, fun _ _ => rfl,
      by rw [Set.inter_self, Set.image_id]⟩
  have hE : IsPreconnected (D \ {z | δ z = 0}) :=
    ManifoldZerosComplementConnected.proof (Fin d) D δ hDc hreg hδ ⟨y₁, hy₁D, hy₁⟩
  have hEsub : D \ {z | δ z = 0} ⊆ A '' T := by
    refine hE.subset_of_closure_inter_subset hopen ?_ ?_
    · obtain ⟨x₀, hx₀S, hx₀U⟩ := hne
      exact ⟨A x₀, ⟨hmaps hx₀S.1, hx₀S.2⟩, x₀, ⟨hx₀S, hx₀U⟩, rfl⟩
    · rintro y ⟨hy, hyD, hyδ⟩
      obtain ⟨x, hxcl, hxXB, rfl⟩ := key y hyD hy
      have hxS : x ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} := ⟨hxXB, hyδ⟩
      rcases hcover hxS with hxU | hxV
      · exact ⟨x, ⟨hxS, hxU⟩, rfl⟩
      · exfalso
        obtain ⟨z, hzV, hzS, hzU⟩ := mem_closure_iff.mp hxcl V hV hxV
        have hz : z ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) := ⟨hzS, hzU, hzV⟩
        rw [hdisj] at hz
        exact hz

  have hwD : A w ∈ D := hmaps hwXB
  have hwE : A w ∈ closure (D \ {z | δ z = 0}) := by
    by_contra hw
    rw [mem_closure_iff_nhds] at hw
    push Not at hw
    obtain ⟨t, ht, hte⟩ := hw
    have hzero : δ =ᶠ[𝓝 (A w)] 0 := by
      filter_upwards [ht, hD.mem_nhds hwD] with y hyt hyD
      by_contra hy
      exact (Set.not_nonempty_iff_eq_empty.mpr hte) ⟨y, hyt, hyD, hy⟩
    exact hy₁ (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc hwD hzero hy₁D)
  obtain ⟨x, hxcl, hxXB, hAx⟩ := key (A w) hwD (closure_mono hEsub hwE)
  rw [← hcentre x hxXB hAx]
  exact hxcl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
