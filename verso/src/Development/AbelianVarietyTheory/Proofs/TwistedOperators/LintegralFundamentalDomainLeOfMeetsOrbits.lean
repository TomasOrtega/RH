import Mathlib
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory

open scoped Pointwise

/- English proof (translation)
Establish `hsub : 𝓕 ⊆ ⋃ γ : Γ, γ • S ∩ 𝓕`. Introduce `g hg`. Take `⟨γ, hγ, hγS⟩` from `hmeet g`. Use `Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hg⟩` and prove the remaining obligations. Use `Set.mem_smul_set.2 ⟨γ * g, hγS, ?_⟩` and prove the remaining obligations.

Use `show (γ⁻¹ : G) * (γ * g) = g`. Use `group`. Combine the equalities or inequalities in the displayed calculation. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Use `congr 1`.

Use function extensionality and compare the values at `g`. Use `show f g = f ((γ⁻¹ : Γ) * g)`. Conclude with `(hinv _ (γ⁻¹ : Γ).2 g).symm`. Use `_ = ∫⁻ g in S, f g ∂ν := (h𝓕.setLIntegral_eq_tsum' f S).symm`.
-/
theorem lintegral_fundamentalDomain_le_of_meets_orbits
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (ν : Measure G) [ν.IsMulLeftInvariant] {𝓕 S : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 ν) (_hS : MeasurableSet S)
    (hmeet : ∀ g, ∃ γ ∈ Γ, γ * g ∈ S) {f : G → ℝ≥0∞} (_hf : Measurable f)
    (hinv : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    ∫⁻ g in 𝓕, f g ∂ν ≤ ∫⁻ g in S, f g ∂ν := by
  have hsub : 𝓕 ⊆ ⋃ γ : Γ, γ • S ∩ 𝓕 := by
    intro g hg
    obtain ⟨γ, hγ, hγS⟩ := hmeet g
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hg⟩
    refine Set.mem_smul_set.2 ⟨γ * g, hγS, ?_⟩
    show (γ⁻¹ : G) * (γ * g) = g
    group
  calc ∫⁻ g in 𝓕, f g ∂ν ≤ ∫⁻ g in ⋃ γ : Γ, γ • S ∩ 𝓕, f g ∂ν := lintegral_mono_set hsub
    _ ≤ ∑' γ : Γ, ∫⁻ g in γ • S ∩ 𝓕, f g ∂ν := lintegral_iUnion_le _ _
    _ = ∑' γ : Γ, ∫⁻ g in γ • S ∩ 𝓕, f (γ⁻¹ • g) ∂ν := by
        refine tsum_congr fun γ => ?_
        congr 1
        funext g
        show f g = f ((γ⁻¹ : Γ) * g)
        exact (hinv _ (γ⁻¹ : Γ).2 g).symm
    _ = ∫⁻ g in S, f g ∂ν := (h𝓕.setLIntegral_eq_tsum' f S).symm

end GlobalTheory
