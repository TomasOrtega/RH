import Mathlib
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `f hf`. Establish `h1 : Submodule.map (T : M →ₗ[ℂ] M) W ≤ W`. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Conclude with `hT g hg`. Establish `h2` using `Submodule.topologicalClosure_map T W`.

Conclude with `Submodule.topologicalClosure_mono h1 (h2 ⟨f, hf, rfl⟩)`.
-/
theorem topologicalClosure_stable_of_continuousLinearMap {M : Type} [TopologicalSpace M] [AddCommGroup M]
    [Module ℂ M] [ContinuousSMul ℂ M] [ContinuousAdd M] (W : Submodule ℂ M) (T : M →L[ℂ] M)
    (hT : ∀ f ∈ W, T f ∈ W) : ∀ f ∈ W.topologicalClosure, T f ∈ W.topologicalClosure := by
  intro f hf
  have h1 : Submodule.map (T : M →ₗ[ℂ] M) W ≤ W := by
    rintro _ ⟨g, hg, rfl⟩
    exact hT g hg
  have h2 := Submodule.topologicalClosure_map T W
  exact Submodule.topologicalClosure_mono h1 (h2 ⟨f, hf, rfl⟩)

/- English proof (translation)
Introduce `E _ _ _ _ _ W hmul hF`. Prove the components needed by the constructor for the conclusion. Introduce `ℓ f f₁ hf hf₁`. Establish `hg : Function.HasTemperateGrowth (fun x : E => ((ℓ x : ℝ) : ℂ))` using `(Complex.ofRealCLM.comp ℓ).hasTemperateGrowth`. Use `set T : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ := SchwartzMap.smulLeftCLM ℂ (fun x : E => ((ℓ x : ℝ) : ℂ)) with hTdef`.

Establish `hTapp : ∀ g : SchwartzMap E ℂ, ∀ x, T g x = (ℓ x : ℂ) * g x`. Introduce `g x`. Rewrite using `[hTdef, SchwartzMap.smulLeftCLM_apply hg]`. Both sides reduce to the same expression. Establish `hTW : ∀ g ∈ W, T g ∈ W` using `fun g hg' => hmul ℓ g (T g) hg' (hTapp g)`.

Establish `hf₁T : f₁ = T f`. Use extensionality with `x`. Rewrite using `[hf₁ x, hTapp f x]`. Rewrite using `[hf₁T]`. Conclude with `topologicalClosure_stable_of_continuousLinearMap W T hTW f hf`.

Introduce `f hf`. Establish `hTW : ∀ g ∈ W, SchwartzMap.fourierTransformCLM ℂ g ∈ W`. Introduce `g hg`. Rewrite using `[SchwartzMap.fourierTransformCLM_apply]`. Conclude with `hF g hg`.

Use `topologicalClosure_stable_of_continuousLinearMap W (SchwartzMap.fourierTransformCLM ℂ) hTW f hf` as an intermediate fact. Rewrite `this` using `[SchwartzMap.fourierTransformCLM_apply]`. Then use the resulting hypothesis.
-/
theorem schwartz_closure_stable_linearForm_fourier :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (W : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) →
    (∀ f ∈ W, 𝓕 f ∈ W) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W.topologicalClosure → (∀ x, f₁ x = (ℓ x : ℂ) * f x) →
      f₁ ∈ W.topologicalClosure) ∧
    (∀ f ∈ W.topologicalClosure, 𝓕 f ∈ W.topologicalClosure) := by
  intro E _ _ _ _ _ W hmul hF
  constructor
  · intro ℓ f f₁ hf hf₁
    have hg : Function.HasTemperateGrowth (fun x : E => ((ℓ x : ℝ) : ℂ)) :=
      (Complex.ofRealCLM.comp ℓ).hasTemperateGrowth
    set T : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
      SchwartzMap.smulLeftCLM ℂ (fun x : E => ((ℓ x : ℝ) : ℂ)) with hTdef
    have hTapp : ∀ g : SchwartzMap E ℂ, ∀ x, T g x = (ℓ x : ℂ) * g x := by
      intro g x
      rw [hTdef, SchwartzMap.smulLeftCLM_apply hg]
      rfl
    have hTW : ∀ g ∈ W, T g ∈ W := fun g hg' => hmul ℓ g (T g) hg' (hTapp g)
    have hf₁T : f₁ = T f := by
      ext x
      rw [hf₁ x, hTapp f x]
    rw [hf₁T]
    exact topologicalClosure_stable_of_continuousLinearMap W T hTW f hf
  · intro f hf
    have hTW : ∀ g ∈ W, SchwartzMap.fourierTransformCLM ℂ g ∈ W := by
      intro g hg
      rw [SchwartzMap.fourierTransformCLM_apply]
      exact hF g hg
    have := topologicalClosure_stable_of_continuousLinearMap W (SchwartzMap.fourierTransformCLM ℂ) hTW f hf
    rwa [SchwartzMap.fourierTransformCLM_apply] at this

end GlobalTheory
