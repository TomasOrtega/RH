import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermRegularDimGe
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionSheetsDense
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicFibreInfinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

/- English proof (translation)
Introduce `σ _ X w d A hX hirr hiso hnd`. Take `⟨N, hN, hsub⟩` from `hS σ X w d A hX hirr hiso hnd`. Use `⟨N, hN, ?_⟩` and prove the remaining obligations. Introduce `x hx e A' O V g hO hV hxV hg hleft hXV`. Assume the negation of the conclusion as `hlt`.

Rewrite `hlt` using `[not_le]`. Take `⟨y, hyV, hyX, O₁, V₁, g₁, hO₁, hV₁, hyV₁, hg₁, hleft₁, hXV₁⟩` from `mem_closure_iff.1 (hsub hx) V hV hxV`. Establish `hy : y ∈ g₁ '' O₁` using `hXV₁ ▸ ⟨hyX, hyV₁⟩`. Take `⟨t₀, ht₀, rfl⟩` from `hy`. Use `set U : Set (Fin d → ℂ) := O₁ ∩ g₁ ⁻¹' V with hUdef`.

Establish `hU : IsOpen U` using `hg₁.continuousOn.isOpen_inter_preimage hO₁ hV`. Establish `hUne : U.Nonempty` using `⟨t₀, ht₀, hyV⟩`. Establish `hdiff : DifferentiableOn ℂ (fun t => A' (g₁ t)) U` using `A'.differentiable.comp_differentiableOn (hg₁.differentiableOn.mono Set.inter_subset_left)`. Establish `hmem : ∀ t ∈ U, ∃ u ∈ O, g₁ t = g u`. Introduce `t ht`.

Establish `h1 : g₁ t ∈ X ∩ V₁` using `hXV₁ ▸ Set.mem_image_of_mem g₁ ht.1`. Establish `h2 : g₁ t ∈ X ∩ V` using `⟨h1.1, ht.2⟩`. Rewrite `h2` using `[hXV]`. Take `⟨u, hu, hgu⟩` from `h2`. Conclude with `⟨u, hu, hgu.symm⟩`.

Take `⟨z, hz⟩` from `HolomorphicFibreInfinite.proof d e U (fun t => A' (g₁ t)) hlt hU hUne hdiff`. Apply `hz` to reduce the goal to its premises. Use `Set.Subsingleton.finite ?_` and prove the remaining obligations. Introduce `t₁ ht₁ t₂ ht₂`. Take `⟨u₁, hu₁, hg1⟩` from `hmem t₁ ht₁.1`.

Take `⟨u₂, hu₂, hg2⟩` from `hmem t₂ ht₂.1`. Establish `hz1 : A' (g₁ t₁) = z` using `ht₁.2`. Establish `hz2 : A' (g₁ t₂) = z` using `ht₂.2`. Rewrite `hz1` using `[hg1, hleft u₁ hu₁]`. Rewrite `hz2` using `[hg2, hleft u₂ hu₂]`.

Establish `hgg : g₁ t₁ = g₁ t₂` using `by rw [hg1, hg2, hz1, hz2]`. Rewrite using `[← hleft₁ t₁ ht₁.1.1, ← hleft₁ t₂ ht₂.1.1, hgg]`.
-/
theorem IrreducibleGermRegularDimGe.proof (hS : FiniteProjectionSheetsDense.Statement) :
    IrreducibleGermRegularDimGe.Statement := by
  intro σ _ X w d A hX hirr hiso hnd
  obtain ⟨N, hN, hsub⟩ := hS σ X w d A hX hirr hiso hnd
  refine ⟨N, hN, ?_⟩
  intro x hx e A' O V g hO hV hxV hg hleft hXV
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨y, hyV, hyX, O₁, V₁, g₁, hO₁, hV₁, hyV₁, hg₁, hleft₁, hXV₁⟩ :=
    mem_closure_iff.1 (hsub hx) V hV hxV
  have hy : y ∈ g₁ '' O₁ := hXV₁ ▸ ⟨hyX, hyV₁⟩
  obtain ⟨t₀, ht₀, rfl⟩ := hy
  set U : Set (Fin d → ℂ) := O₁ ∩ g₁ ⁻¹' V with hUdef
  have hU : IsOpen U := hg₁.continuousOn.isOpen_inter_preimage hO₁ hV
  have hUne : U.Nonempty := ⟨t₀, ht₀, hyV⟩
  have hdiff : DifferentiableOn ℂ (fun t => A' (g₁ t)) U :=
    A'.differentiable.comp_differentiableOn (hg₁.differentiableOn.mono Set.inter_subset_left)

  have hmem : ∀ t ∈ U, ∃ u ∈ O, g₁ t = g u := by
    intro t ht
    have h1 : g₁ t ∈ X ∩ V₁ := hXV₁ ▸ Set.mem_image_of_mem g₁ ht.1
    have h2 : g₁ t ∈ X ∩ V := ⟨h1.1, ht.2⟩
    rw [hXV] at h2
    obtain ⟨u, hu, hgu⟩ := h2
    exact ⟨u, hu, hgu.symm⟩
  obtain ⟨z, hz⟩ := HolomorphicFibreInfinite.proof d e U (fun t => A' (g₁ t)) hlt hU hUne hdiff
  apply hz
  refine Set.Subsingleton.finite ?_
  intro t₁ ht₁ t₂ ht₂
  obtain ⟨u₁, hu₁, hg1⟩ := hmem t₁ ht₁.1
  obtain ⟨u₂, hu₂, hg2⟩ := hmem t₂ ht₂.1
  have hz1 : A' (g₁ t₁) = z := ht₁.2
  have hz2 : A' (g₁ t₂) = z := ht₂.2
  rw [hg1, hleft u₁ hu₁] at hz1
  rw [hg2, hleft u₂ hu₂] at hz2
  have hgg : g₁ t₁ = g₁ t₂ := by rw [hg1, hg2, hz1, hz2]
  rw [← hleft₁ t₁ ht₁.1.1, ← hleft₁ t₂ ht₂.1.1, hgg]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
