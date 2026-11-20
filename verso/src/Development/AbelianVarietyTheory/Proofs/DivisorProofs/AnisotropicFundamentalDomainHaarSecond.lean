import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicDoubleCosetFinite
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.DefCovol

open scoped Pointwise

/- English proof (translation)
Use `⟨?_, fun φ hφ hinv => ?_⟩` and prove the remaining obligations. Establish `hsub : 𝓕 ⊆ ⋃ γ : Γ, γ • C ∩ 𝓕`. Introduce `x hx`. Take `⟨γ, hγ, s, hs, rfl⟩` from `hcov x`. Conclude with `Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, Set.mem_smul_set.2 ⟨s, hs, rfl⟩, hx⟩`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨M, hM⟩` from `hC.exists_bound_of_continuousOn hφ.continuousOn`. Use `⟨M, fun h => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, s, hs, rfl⟩` from `hcov h`. Rewrite using `[hinv γ hγ s]`.

Conclude with `hM s hs`.
-/
theorem of_compact_cover {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [Countable Γ] (C : Set G) (hC : IsCompact C)
    (hcov : ∀ h : G, ∃ γ ∈ Γ, ∃ s ∈ C, h = γ * s) (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    μ 𝓕 < ⊤ ∧ ∀ φ : G → ℂ, Continuous φ → (∀ γ ∈ Γ, ∀ h, φ (γ * h) = φ h) → ∃ M : ℝ, ∀ h, ‖φ h‖ ≤ M := by
  refine ⟨?_, fun φ hφ hinv => ?_⟩
  · have hsub : 𝓕 ⊆ ⋃ γ : Γ, γ • C ∩ 𝓕 := by
      intro x hx
      obtain ⟨γ, hγ, s, hs, rfl⟩ := hcov x
      exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, Set.mem_smul_set.2 ⟨s, hs, rfl⟩, hx⟩
    calc μ 𝓕 ≤ μ (⋃ γ : Γ, γ • C ∩ 𝓕) := measure_mono hsub
      _ ≤ ∑' γ : Γ, μ (γ • C ∩ 𝓕) := measure_iUnion_le _
      _ = μ C := (h𝓕.measure_eq_tsum C).symm
      _ < ⊤ := hC.measure_lt_top
  · obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hφ.continuousOn
    refine ⟨M, fun h => ?_⟩
    obtain ⟨γ, hγ, s, hs, rfl⟩ := hcov h
    rw [hinv γ hγ s]
    exact hM s hs

end GlobalTheory.ThK.DefCovol

end
