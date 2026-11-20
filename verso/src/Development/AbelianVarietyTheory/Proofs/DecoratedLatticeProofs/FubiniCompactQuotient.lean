import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

open scoped Pointwise

namespace GlobalTheory

/- English proof (translation)
Introduce `H _ _ _ _ _ _ _ _ μ _ Γ hΓc hΓd hK 𝓕 h𝓕 X _ m _ f hf hinv hB`. Take `⟨K, hKc, hKcov⟩` from `hK`. Take `⟨B, hB⟩` from `hB K hKc`. Use `haveI : Countable Γ := hΓc`. Establish `hbd : ∀ h, ∫⁻ x, ‖f h x‖ₑ ∂m ≤ B`.

Introduce `h`. Take `⟨γ, hγ, hk⟩` from `hKcov h`. Use `hB _ hk` as an intermediate fact. Simplify `this` using `only [hinv γ hγ h]`. Establish `hfin : μ 𝓕 < ⊤`.

Establish `hcover : 𝓕 ⊆ ⋃ g : Γ, (g • K)`. Introduce `h _`. Take `⟨γ, hγ, hk⟩` from `hKcov h`. Use `Set.mem_iUnion.2 ⟨⟨γ, hγ⟩⁻¹, ?_⟩` and prove the remaining obligations. Use `Set.mem_smul_set.2 ⟨γ * h, hk, ?_⟩` and prove the remaining obligations.

Simplify using `[Subgroup.smul_def]`. Establish `hle : μ 𝓕 ≤ μ K`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Set.inter_eq_right.2 hcover]`. Use `_ = μ (⋃ g : Γ, (g • K ∩ 𝓕)) := by rw [Set.iUnion_inter]`.

Use `_ ≤ ∑' g : Γ, μ (g • K ∩ 𝓕) := measure_iUnion_le _`. Use `_ = μ K := (h𝓕.measure_eq_tsum K).symm`. Conclude with `hle.trans_lt hKc.measure_lt_top`. Use `⟨hf.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Establish `hm : AEMeasurable (fun z : H × X => ‖Function.uncurry f z‖ₑ) ((μ.restrict 𝓕).prod m)` using `hf.enorm.aemeasurable`.

Rewrite using `[HasFiniteIntegral, lintegral_prod _ hm]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fubini_compact_quotient : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure] (Γ : Subgroup H), Countable Γ → DiscreteTopology Γ → (∃ K : Set H, IsCompact K ∧ ∀ g, ∃ γ ∈ Γ, γ * g ∈ K) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 μ → ∀ (X : Type) [MeasurableSpace X] (m : Measure X) [SFinite m] (f : H → X → ℂ), Measurable (Function.uncurry f) → (∀ γ ∈ Γ, ∀ h x, f (γ * h) x = f h x) → (∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ h ∈ K, ∫⁻ x, ‖f h x‖ₑ ∂m ≤ B) → Integrable (Function.uncurry f) ((μ.restrict 𝓕).prod m) := by
  intro H _ _ _ _ _ _ _ _ μ _ Γ hΓc hΓd hK 𝓕 h𝓕 X _ m _ f hf hinv hB
  obtain ⟨K, hKc, hKcov⟩ := hK
  obtain ⟨B, hB⟩ := hB K hKc
  haveI : Countable Γ := hΓc

  have hbd : ∀ h, ∫⁻ x, ‖f h x‖ₑ ∂m ≤ B := by
    intro h
    obtain ⟨γ, hγ, hk⟩ := hKcov h
    have := hB _ hk
    simpa only [hinv γ hγ h] using this

  have hfin : μ 𝓕 < ⊤ := by
    have hcover : 𝓕 ⊆ ⋃ g : Γ, (g • K) := by
      intro h _
      obtain ⟨γ, hγ, hk⟩ := hKcov h
      refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩⁻¹, ?_⟩
      refine Set.mem_smul_set.2 ⟨γ * h, hk, ?_⟩
      simp [Subgroup.smul_def]
    have hle : μ 𝓕 ≤ μ K := by
      calc μ 𝓕 = μ ((⋃ g : Γ, (g • K)) ∩ 𝓕) := by
              rw [Set.inter_eq_right.2 hcover]
        _ = μ (⋃ g : Γ, (g • K ∩ 𝓕)) := by rw [Set.iUnion_inter]
        _ ≤ ∑' g : Γ, μ (g • K ∩ 𝓕) := measure_iUnion_le _
        _ = μ K := (h𝓕.measure_eq_tsum K).symm
    exact hle.trans_lt hKc.measure_lt_top
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have hm : AEMeasurable (fun z : H × X => ‖Function.uncurry f z‖ₑ) ((μ.restrict 𝓕).prod m) :=
    hf.enorm.aemeasurable
  rw [HasFiniteIntegral, lintegral_prod _ hm]
  calc ∫⁻ h, ∫⁻ x, ‖Function.uncurry f (h, x)‖ₑ ∂m ∂(μ.restrict 𝓕)
      ≤ ∫⁻ _, (B : ENNReal) ∂(μ.restrict 𝓕) := lintegral_mono (fun h => hbd h)
    _ = B * μ 𝓕 := by simp
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hfin

end GlobalTheory
