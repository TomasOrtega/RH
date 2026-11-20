import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ G L f hf`. Take `⟨-, -, -, S, hS⟩` from `hf`. Establish `hK : IsCompact ((L.K.toSubgroup : Subgroup G.GAf) : Set G.GAf)` using `L.compact`. Use `⟨⋃ s ∈ S, (fun ab : G.GAf × G.GAf => ab.1 * s * ab.2) '' ((L.K.toSubgroup : Set G.GAf) ×ˢ (L.K.toSubgroup : Set G.GAf)), ?_, ?_⟩` and prove the remaining obligations. Use `S.isCompact_biUnion fun s _ => (hK.prod hK).image ?_ fun_prop` and prove the remaining obligations.

Introduce `g hg`. Take `⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩` from `hS g hg`. Conclude with `Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩`.
-/
theorem isTest_support_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  intro p _ G L f hf
  obtain ⟨-, -, -, S, hS⟩ := hf
  have hK : IsCompact ((L.K.toSubgroup : Subgroup G.GAf) : Set G.GAf) := L.compact
  refine ⟨⋃ s ∈ S, (fun ab : G.GAf × G.GAf => ab.1 * s * ab.2) ''
      ((L.K.toSubgroup : Set G.GAf) ×ˢ (L.K.toSubgroup : Set G.GAf)), ?_, ?_⟩
  · refine S.isCompact_biUnion fun s _ => (hK.prod hK).image ?_
    fun_prop
  · intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
    exact Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩

end GlobalTheory
