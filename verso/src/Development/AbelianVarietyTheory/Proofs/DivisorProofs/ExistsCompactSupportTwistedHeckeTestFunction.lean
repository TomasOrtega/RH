import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

/- English proof (translation)
Introduce `p _ G L f hf`. Take `⟨S, hS⟩` from `hf.2.2.2`. Use `⟨⋃ s ∈ S, (fun q : G.GAf × G.GAf => q.1 * s * q.2) '' ((L.K : Set G.GAf) ×ˢ (L.K : Set G.GAf)), ?_, ?_⟩` and prove the remaining obligations. Use `S.isCompact_biUnion fun s _ => ?_` and prove the remaining obligations. Conclude with `(L.compact.prod L.compact).image (by fun_prop)`.

Introduce `g hg`. Take `⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩` from `hS g hg`. Conclude with `Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩`.
-/
theorem support_subset_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  intro p _ G L f hf
  obtain ⟨S, hS⟩ := hf.2.2.2
  refine ⟨⋃ s ∈ S, (fun q : G.GAf × G.GAf => q.1 * s * q.2) '' ((L.K : Set G.GAf) ×ˢ (L.K : Set G.GAf)), ?_, ?_⟩
  · refine S.isCompact_biUnion fun s _ => ?_
    exact (L.compact.prod L.compact).image (by fun_prop)
  · intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
    exact Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩

end GlobalTheory.FinClsLoc
