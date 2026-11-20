import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ H τ a`. Establish `hM : (nonZeroDivisors (𝓞 E)).map (τ : 𝓞 E →* 𝓞 E) = nonZeroDivisors (𝓞 E)`. Conclude with `MulEquivClass.map_nonZeroDivisors τ`. Set `τE : E ≃+* E` to `IsLocalization.ringEquivOfRingEquiv E E τ hM`. Establish `hτE : ∀ x : 𝓞 E, τE (x : E) = ((τ x : 𝓞 E) : E)`.

Introduce `x`. Conclude with `IsLocalization.ringEquivOfRingEquiv_eq hM x`. Take `⟨ψ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[← hτE, H.bar_eq, H.bar_eq, ← hτE]`.

Apply `ψ.injective` to reduce the goal to its premises. Establish `h1` using `IsCMField.complexEmbedding_complexConj E (ψ.comp (τE : E →+* E)) (a : E)`. Establish `h2` using `IsCMField.complexEmbedding_complexConj E ψ (τE (a : E))`. Simplify using `only [RingHom.comp_apply, RingEquiv.coe_toRingHom] at h1`. Rewrite using `[h1, h2]`.
-/
theorem ringOfIntegers_equiv_bar_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (τ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E), τ (H.bar a) = H.bar (τ a) := by
  intro E _ _ _ H τ a
  have hM : (nonZeroDivisors (𝓞 E)).map (τ : 𝓞 E →* 𝓞 E) = nonZeroDivisors (𝓞 E) := by
    exact MulEquivClass.map_nonZeroDivisors τ
  let τE : E ≃+* E := IsLocalization.ringEquivOfRingEquiv E E τ hM
  have hτE : ∀ x : 𝓞 E, τE (x : E) = ((τ x : 𝓞 E) : E) := by
    intro x
    exact IsLocalization.ringEquivOfRingEquiv_eq hM x
  obtain ⟨ψ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply RingOfIntegers.ext
  rw [← hτE, H.bar_eq, H.bar_eq, ← hτE]
  apply ψ.injective
  have h1 := IsCMField.complexEmbedding_complexConj E (ψ.comp (τE : E →+* E)) (a : E)
  have h2 := IsCMField.complexEmbedding_complexConj E ψ (τE (a : E))
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom] at h1
  rw [h1, h2]

end GlobalTheory
