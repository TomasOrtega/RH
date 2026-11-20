import Mathlib

/- English proof (translation)
Introduce `G K _ _ _ _ _ _ _ κ _ a p ha hp φ ψ hφ hψ h1 h2 g`. Establish `key : ∀ f : G → ℂ, Continuous f → MeasureTheory.Integrable (fun k => p k * f (g * a k)) κ`. Introduce `f hf`. Establish `hc : Continuous (fun k => p k * f (g * a k))` using `hp.mul (hf.comp (continuous_const.mul ha))`. Conclude with `(BoundedContinuousFunction.mkOfCompact ⟨_, hc⟩).integrable κ`.

Simplify using `only [Pi.add_apply, mul_add]`. Rewrite using `[MeasureTheory.integral_add (key φ hφ) (key ψ hψ), h1 g, h2 g]`.
-/
theorem UpperTheory.mean_value_uniqueness :
    ∀ {G K : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace K] [CompactSpace K]
        [MeasurableSpace K] [OpensMeasurableSpace K] (κ : MeasureTheory.Measure K) [MeasureTheory.IsFiniteMeasure κ]
        (a : K → G) (p : K → ℂ), Continuous a → Continuous p → ∀ φ ψ : G → ℂ, Continuous φ → Continuous ψ →
        (∀ g, ∫ k, p k * φ (g * a k) ∂κ = φ g) → (∀ g, ∫ k, p k * ψ (g * a k) ∂κ = ψ g) →
        ∀ g, ∫ k, p k * (φ + ψ) (g * a k) ∂κ = (φ + ψ) g := by
  intro G K _ _ _ _ _ _ _ κ _ a p ha hp φ ψ hφ hψ h1 h2 g
  have key : ∀ f : G → ℂ, Continuous f →
      MeasureTheory.Integrable (fun k => p k * f (g * a k)) κ := by
    intro f hf
    have hc : Continuous (fun k => p k * f (g * a k)) :=
      hp.mul (hf.comp (continuous_const.mul ha))
    exact (BoundedContinuousFunction.mkOfCompact ⟨_, hc⟩).integrable κ
  simp only [Pi.add_apply, mul_add]
  rw [MeasureTheory.integral_add (key φ hφ) (key ψ hψ), h1 g, h2 g]
