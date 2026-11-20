import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermProjectionOpenNear
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedFibreNear
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermProjectionImageNear
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteGermProjectionOpenAt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

/- English proof (translation)
Introduce `σ _ X w d A hX hirr hisow hinj`. Take `⟨N₁, hN₁, h₁⟩` from `hiso σ X w d A hX hisow`. Take `⟨N₂, hN₂, h₂⟩` from `himg σ X w d A hX hirr hisow hinj`. Take `⟨N, k, f, hNo, hwN, hf, hXN⟩` from `hX`. Use `⟨N₁ ∩ N₂ ∩ N, Filter.inter_mem (Filter.inter_mem hN₁ hN₂) (hNo.mem_nhds hwN), ?_⟩` and prove the remaining obligations.

Introduce and unpack `x ⟨hxX, ⟨hx₁, hx₂⟩, hxN⟩ V hV`. Establish `hXx : IsAnalyticNear X x` using `⟨N, k, f, hNo, hxN, hf, hXN⟩`. Conclude with `hopen σ X x d A hXx (h₁ x ⟨hxX, hx₁⟩) (h₂ x ⟨hxX, hx₂⟩) V hV`.
-/
theorem IrreducibleGermProjectionOpenNear.proof (hiso : IsolatedFibreNear.Statement)
    (himg : IrreducibleGermProjectionImageNear.Statement) (hopen : FiniteGermProjectionOpenAt.Statement) :
    IrreducibleGermProjectionOpenNear.Statement := by
  intro σ _ X w d A hX hirr hisow hinj
  obtain ⟨N₁, hN₁, h₁⟩ := hiso σ X w d A hX hisow
  obtain ⟨N₂, hN₂, h₂⟩ := himg σ X w d A hX hirr hisow hinj
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  refine ⟨N₁ ∩ N₂ ∩ N, Filter.inter_mem (Filter.inter_mem hN₁ hN₂) (hNo.mem_nhds hwN), ?_⟩
  rintro x ⟨hxX, ⟨hx₁, hx₂⟩, hxN⟩ V hV

  have hXx : IsAnalyticNear X x := ⟨N, k, f, hNo, hxN, hf, hXN⟩
  exact hopen σ X x d A hXx (h₁ x ⟨hxX, hx₁⟩) (h₂ x ⟨hxX, hx₂⟩) V hV

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
