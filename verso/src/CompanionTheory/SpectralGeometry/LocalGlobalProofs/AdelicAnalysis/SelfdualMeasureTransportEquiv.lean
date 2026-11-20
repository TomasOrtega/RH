import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

/- English proof (translation)
Take `⟨hH, hF⟩` from `h`. Set `eM : V ≃ᵐ V'` to `e.toHomeomorph.toMeasurableEquiv`. Establish `hcoe : (eM : V → V') = e` using `rfl`. Establish `hint : ∀ g : V' → ℂ, ∫ y, g y ∂(μ.map e) = ∫ x, g (e x) ∂μ` using `fun g => by`. Rewrite using `[← hcoe]`.

Conclude with `integral_map_equiv eM g`. Use `⟨e.isAddHaarMeasure_map μ, fun Φ hc hs hi z => ?_⟩` and prove the remaining obligations. Establish `hinner : ∀ y : V, ∫ x, Φ x * χ x (e y) ∂(μ.map e) = ∫ x, (Φ ∘ e) x * χ (e x) (e y) ∂μ` using `fun y => hint _`. Establish `hi' : Integrable (fun y => ∫ x, (Φ ∘ e) x * χ (e x) (e y) ∂μ) μ`. Establish `h1 : Integrable ((fun y => ∫ x, Φ x * χ x y ∂(μ.map e)) ∘ eM) μ` using `(eM.measurableEmbedding.integrable_map_iff).1 (by rw [hcoe]; exact hi)`.

Use `h1.congr (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Conclude with `hinner y`. Establish `hcs : HasCompactSupport (Φ ∘ e)` using `hs.comp_homeomorph e.toHomeomorph`. Establish `key` using `hF (Φ ∘ e) (hc.comp e.continuous) hcs hi' (e.symm z)`. Rewrite using `[hint]`.

Simplify using `only [hinner]`. Simplify using `using key`.
-/
theorem selfDual_map_of_comp {V V' : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V']
    (e : V ≃ₜ+ V') (μ : Measure V) (χ : V' → V' → ℂ)
    (h : SelfDual μ (fun x y => χ (e x) (e y))) : SelfDual (μ.map e) χ := by
  obtain ⟨hH, hF⟩ := h
  let eM : V ≃ᵐ V' := e.toHomeomorph.toMeasurableEquiv
  have hcoe : (eM : V → V') = e := rfl
  have hint : ∀ g : V' → ℂ, ∫ y, g y ∂(μ.map e) = ∫ x, g (e x) ∂μ := fun g => by
    rw [← hcoe]; exact integral_map_equiv eM g
  refine ⟨e.isAddHaarMeasure_map μ, fun Φ hc hs hi z => ?_⟩
  have hinner : ∀ y : V, ∫ x, Φ x * χ x (e y) ∂(μ.map e)
      = ∫ x, (Φ ∘ e) x * χ (e x) (e y) ∂μ := fun y => hint _
  have hi' : Integrable (fun y => ∫ x, (Φ ∘ e) x * χ (e x) (e y) ∂μ) μ := by
    have h1 : Integrable ((fun y => ∫ x, Φ x * χ x y ∂(μ.map e)) ∘ eM) μ :=
      (eM.measurableEmbedding.integrable_map_iff).1 (by rw [hcoe]; exact hi)
    refine h1.congr (Filter.Eventually.of_forall fun y => ?_)
    exact hinner y
  have hcs : HasCompactSupport (Φ ∘ e) :=
    hs.comp_homeomorph e.toHomeomorph
  have key := hF (Φ ∘ e) (hc.comp e.continuous) hcs hi' (e.symm z)
  rw [hint]
  simp only [hinner]
  simpa using key

/- English proof (translation)
Use `⟨selfDual_map_of_comp e μ χ, fun h => ?_⟩` and prove the remaining obligations. Establish `h2` using `selfDual_map_of_comp e.symm (μ.map e) (fun x y => χ (e x) (e y)) (by simpa using h)`. Establish `hm : (μ.map e).map e.symm = μ`. Establish `m1 : Measurable (e.symm : V' → V)` using `e.symm.continuous.measurable`. Establish `m2 : Measurable (e : V → V')` using `e.continuous.measurable`.

Rewrite using `[Measure.map_map m1 m2]`. Establish `: (e.symm : V' → V) ∘ e = id` using `by ext x; simp`. Rewrite using `[this, Measure.map_id]`. Rewrite `h2` using `[hm]`. Then use the resulting hypothesis.
-/
theorem selfDual_transport (V V' : Type) [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V']
    (e : V ≃ₜ+ V') (μ : Measure V) (χ : V' → V' → ℂ) :
    SelfDual μ (fun x y => χ (e x) (e y)) ↔ SelfDual (μ.map e) χ := by
  refine ⟨selfDual_map_of_comp e μ χ, fun h => ?_⟩
  have h2 := selfDual_map_of_comp e.symm (μ.map e) (fun x y => χ (e x) (e y)) (by simpa using h)
  have hm : (μ.map e).map e.symm = μ := by
    have m1 : Measurable (e.symm : V' → V) := e.symm.continuous.measurable
    have m2 : Measurable (e : V → V') := e.continuous.measurable
    rw [Measure.map_map m1 m2]
    have : (e.symm : V' → V) ∘ e = id := by ext x; simp
    rw [this, Measure.map_id]
  rwa [hm] at h2

end GlobalTheory.CompanionTheory.SW
