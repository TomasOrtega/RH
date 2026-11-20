import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated

open MeasureTheory Filter
open scoped Topology

namespace GlobalTheory.CompanionTheory.Param

/- English proof (translation)
Introduce `Y T _ _ _ _ _ μ U hU F hF hdiff hdom`. Establish `hGat : ∀ z ∈ U, ∀ (t : T) (y : Y), ContinuousAt (fun u : ℂ × T × Y => F u.1 u.2.1 u.2.2) (z, t, y)` using `fun z hz t y => hF.continuousAt ((hU.prod isOpen_univ).mem_nhds (Set.mk_mem_prod hz (Set.mem_univ _)))`. Establish `hslice : ∀ z ∈ U, ∀ t : T, Continuous (fun y => F z t y)` using `fun z hz t => hF.comp_continuous (f := fun y : Y => (z, t, y)) (by fun_prop) fun y => Set.mk_mem_prod hz (Set.mem_univ _)`. Use `⟨?_, fun t => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨z₀, t₀⟩ ⟨hz₀, -⟩`.

Take `⟨V, hV, N, hN, w, hw, hbound⟩` from `hdom z₀ hz₀ t₀`. Use `ContinuousAt.continuousWithinAt ?_` and prove the remaining obligations. Use `MeasureTheory.continuousAt_of_dominated (bound := w) ?_ ?_ hw ?_` and prove the remaining obligations. Establish `hmem : U ×ˢ (Set.univ : Set T) ∈ 𝓝 (z₀, t₀)` using `(hU.prod isOpen_univ).mem_nhds (Set.mk_mem_prod hz₀ (Set.mem_univ _)) filter_upwards [hmem] with x hx`. Conclude with `(hslice x.1 hx.1 x.2).aestronglyMeasurable`.

Establish `hmem : V ×ˢ N ∈ 𝓝 (z₀, t₀)`. Rewrite using `[nhds_prod_eq]`. Conclude with `Filter.prod_mem_prod hV hN`. Use `filter_upwards [hmem] with x hx`. Conclude with `Filter.Eventually.of_forall fun y => hbound x.1 hx.1 x.2 hx.2 y`.

Conclude with `Filter.Eventually.of_forall fun y => ContinuousAt.comp_of_eq (f := fun x : ℂ × T => (x.1, x.2, y)) (hGat z₀ hz₀ t₀ y) (by fun_prop) rfl`. Take `⟨h, -⟩` from `GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated (μ := μ) (F := fun y z => F z t y) hU (fun z hz => (hslice z hz t).aestronglyMeasurable) (Filter.Eventually.of_forall fun y => hdiff t y) (fun z hz => by`. Take `⟨V, hV, N, hN, w, hw, hb⟩` from `hdom z hz t`. Conclude with `⟨V, hV, w, hw, Filter.Eventually.of_forall fun y z' hz' => hb z' hz' t (mem_of_mem_nhds hN) y⟩)`. Conclude with `h`.
-/
theorem continuousOn_differentiableOn_integral :
    ∀ {Y T : Type} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
      [TopologicalSpace T] [FirstCountableTopology T] (μ : Measure Y) (U : Set ℂ), IsOpen U →
      ∀ F : ℂ → T → Y → ℂ,
      ContinuousOn (fun u : ℂ × T × Y => F u.1 u.2.1 u.2.2) (U ×ˢ Set.univ) →
      (∀ t y, DifferentiableOn ℂ (fun z => F z t y) U) →
      (∀ z₀ ∈ U, ∀ t₀ : T, ∃ V ∈ 𝓝 z₀, ∃ N ∈ 𝓝 t₀, ∃ w : Y → ℝ, Integrable w μ ∧
        ∀ z ∈ V, ∀ t ∈ N, ∀ y, ‖F z t y‖ ≤ w y) →
      ContinuousOn (fun u : ℂ × T => ∫ y, F u.1 u.2 y ∂μ) (U ×ˢ Set.univ) ∧
        ∀ t, DifferentiableOn ℂ (fun z => ∫ y, F z t y ∂μ) U := by
  intro Y T _ _ _ _ _ μ U hU F hF hdiff hdom
  have hGat : ∀ z ∈ U, ∀ (t : T) (y : Y),
      ContinuousAt (fun u : ℂ × T × Y => F u.1 u.2.1 u.2.2) (z, t, y) := fun z hz t y =>
    hF.continuousAt ((hU.prod isOpen_univ).mem_nhds (Set.mk_mem_prod hz (Set.mem_univ _)))
  have hslice : ∀ z ∈ U, ∀ t : T, Continuous (fun y => F z t y) := fun z hz t =>
    hF.comp_continuous (f := fun y : Y => (z, t, y)) (by fun_prop)
      fun y => Set.mk_mem_prod hz (Set.mem_univ _)
  refine ⟨?_, fun t => ?_⟩
  · rintro ⟨z₀, t₀⟩ ⟨hz₀, -⟩
    obtain ⟨V, hV, N, hN, w, hw, hbound⟩ := hdom z₀ hz₀ t₀
    refine ContinuousAt.continuousWithinAt ?_
    refine MeasureTheory.continuousAt_of_dominated (bound := w) ?_ ?_ hw ?_
    · have hmem : U ×ˢ (Set.univ : Set T) ∈ 𝓝 (z₀, t₀) :=
        (hU.prod isOpen_univ).mem_nhds (Set.mk_mem_prod hz₀ (Set.mem_univ _))
      filter_upwards [hmem] with x hx
      exact (hslice x.1 hx.1 x.2).aestronglyMeasurable
    · have hmem : V ×ˢ N ∈ 𝓝 (z₀, t₀) := by
        rw [nhds_prod_eq]
        exact Filter.prod_mem_prod hV hN
      filter_upwards [hmem] with x hx
      exact Filter.Eventually.of_forall fun y => hbound x.1 hx.1 x.2 hx.2 y
    · exact Filter.Eventually.of_forall fun y =>
        ContinuousAt.comp_of_eq (f := fun x : ℂ × T => (x.1, x.2, y)) (hGat z₀ hz₀ t₀ y)
          (by fun_prop) rfl
  · obtain ⟨h, -⟩ := GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated (μ := μ)
      (F := fun y z => F z t y) hU (fun z hz => (hslice z hz t).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => hdiff t y) (fun z hz => by
        obtain ⟨V, hV, N, hN, w, hw, hb⟩ := hdom z hz t
        exact ⟨V, hV, w, hw, Filter.Eventually.of_forall fun y z' hz' =>
          hb z' hz' t (mem_of_mem_nhds hN) y⟩)
    exact h

end GlobalTheory.CompanionTheory.Param
