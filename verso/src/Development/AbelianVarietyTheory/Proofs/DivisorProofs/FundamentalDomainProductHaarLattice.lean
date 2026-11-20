import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolValueAtIntegralOfExpansion
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox

noncomputable section

namespace GlobalTheory.DblBox

/- English proof (translation)
The claim follows from `(GlobalTheory.DefDoubling.measure_le_of_cover h𝓕 (C := C) fun x => by obtain ⟨γ, hγ, c, hcC, rfl⟩ := hc x exact ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, by simpa using hcC⟩).trans_lt hC.measure_lt_top`.
-/
theorem fundDomain_measure_lt_top_of_cocompact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] {Γ : Subgroup G} [Countable Γ] {μ : Measure G} [μ.IsHaarMeasure]
    {𝓕 C : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C) (hc : ∀ g, ∃ γ ∈ Γ, ∃ c ∈ C, g = γ * c) :
    μ 𝓕 < ⊤ :=
  (GlobalTheory.DefDoubling.measure_le_of_cover h𝓕 (C := C) fun x => by
    obtain ⟨γ, hγ, c, hcC, rfl⟩ := hc x
    exact ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, by simpa using hcC⟩).trans_lt hC.measure_lt_top

/- English proof (translation)
Introduce `G H _ _ _ _ _ _ _ _ _ _ _ _ Γ Δ _ _ μ ν hμ hν 𝓕 𝓖 h𝓕 h𝓖 ⟨C, hC, hc⟩ ⟨D, hD, hd⟩ θ hθ hinv h0`. Use `haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (fundDomain_measure_lt_top_of_cocompact h𝓕 hC hc).ne`. Use `haveI : IsFiniteMeasure (ν.restrict 𝓖) := isFiniteMeasure_restrict.2 (fundDomain_measure_lt_top_of_cocompact h𝓖 hD hd).ne`. Take `⟨M, hM⟩` from `(hC.prod hD).exists_bound_of_continuousOn hθ.continuousOn`. Establish `hb : ∀ p : G × H, ‖θ p.1 p.2‖ ≤ M` using `fun p => by`.

Take `⟨γ, hγ, c, hcC, e1⟩` from `hc p.1`. Take `⟨δ, hδ, d, hdD, e2⟩` from `hd p.2`. Rewrite using `[e1, e2, hinv γ hγ δ hδ]`. Conclude with `hM (c, d) ⟨hcC, hdD⟩`. Establish `hi : Integrable (Function.uncurry θ) ((μ.restrict 𝓕).prod (ν.restrict 𝓖))` using `Integrable.of_bound hθ.aestronglyMeasurable M (Eventually.of_forall hb)`.

Simplify using `only [setAverage_eq]`. Rewrite using `[integral_smul, integral_integral_swap hi]`. Simplify using `[h0]`.
-/
theorem integral_setAverage_eq_zero_of_cocompact : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (Γ : Subgroup G) (Δ : Subgroup H) [Countable Γ] [Countable Δ] (μ : Measure G) (ν : Measure H), μ.IsHaarMeasure → ν.IsHaarMeasure →
    ∀ (𝓕 : Set G) (𝓖 : Set H), IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Δ 𝓖 ν →
    (∃ C : Set G, IsCompact C ∧ ∀ g, ∃ γ ∈ Γ, ∃ c ∈ C, g = γ * c) → (∃ C : Set H, IsCompact C ∧ ∀ h, ∃ γ ∈ Δ, ∃ c ∈ C, h = γ * c) →
    ∀ θ : G → H → ℂ, Continuous (fun p : G × H => θ p.1 p.2) → (∀ γ ∈ Γ, ∀ δ ∈ Δ, ∀ g h, θ (γ * g) (δ * h) = θ g h) →
    (∀ h, ∫ g in 𝓕, θ g h ∂μ = 0) → ∫ g in 𝓕, (⨍ h in 𝓖, θ g h ∂ν) ∂μ = 0 := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ Γ Δ _ _ μ ν hμ hν 𝓕 𝓖 h𝓕 h𝓖 ⟨C, hC, hc⟩ ⟨D, hD, hd⟩ θ hθ hinv h0
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (fundDomain_measure_lt_top_of_cocompact h𝓕 hC hc).ne
  haveI : IsFiniteMeasure (ν.restrict 𝓖) :=
    isFiniteMeasure_restrict.2 (fundDomain_measure_lt_top_of_cocompact h𝓖 hD hd).ne
  obtain ⟨M, hM⟩ := (hC.prod hD).exists_bound_of_continuousOn hθ.continuousOn
  have hb : ∀ p : G × H, ‖θ p.1 p.2‖ ≤ M := fun p => by
    obtain ⟨γ, hγ, c, hcC, e1⟩ := hc p.1
    obtain ⟨δ, hδ, d, hdD, e2⟩ := hd p.2
    rw [e1, e2, hinv γ hγ δ hδ]
    exact hM (c, d) ⟨hcC, hdD⟩
  have hi : Integrable (Function.uncurry θ) ((μ.restrict 𝓕).prod (ν.restrict 𝓖)) :=
    Integrable.of_bound hθ.aestronglyMeasurable M (Eventually.of_forall hb)
  simp only [setAverage_eq]
  rw [integral_smul, integral_integral_swap hi]
  simp [h0]

end GlobalTheory.DblBox
