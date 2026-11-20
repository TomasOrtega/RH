import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

/- English proof (translation)
Introduce `r hr`. Take `⟨n, a, b, c, hs, hc⟩` from `hU r hr`. Establish `hfix : ∀ x : L, x ∈ Fix L U → x ∈ Fix L (U.subgroupOf H)`. Introduce `x hx σ`. Conclude with `hx ⟨(σ.1 : G), Subgroup.mem_subgroupOf.mp σ.2⟩`.

Use `⟨n, a, b, c, ⟨fun i => hfix _ (hs.a_mem i), fun i => hfix _ (hs.b_mem i), hfix _ hs.c_mem, hs.a_le, hs.b_le, hs.c_le, ?_, ?_⟩, hc⟩` and prove the remaining obligations. Introduce `σ hσ`. Conclude with `hs.sum_in (σ : G) (Subgroup.mem_subgroupOf.mp hσ)`. Introduce `σ hσ`. Conclude with `hs.sum_out (σ : G) (fun h => hσ (Subgroup.mem_subgroupOf.mpr h))`.
-/
theorem almostSep_subgroupOf (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L] (U H : Subgroup G) (hU : AlmostSep v U) :
    AlmostSep v (U.subgroupOf H) := by
  intro r hr
  obtain ⟨n, a, b, c, hs, hc⟩ := hU r hr
  have hfix : ∀ x : L, x ∈ Fix L U → x ∈ Fix L (U.subgroupOf H) := by
    intro x hx σ
    exact hx ⟨(σ.1 : G), Subgroup.mem_subgroupOf.mp σ.2⟩
  refine ⟨n, a, b, c, ⟨fun i => hfix _ (hs.a_mem i), fun i => hfix _ (hs.b_mem i),
    hfix _ hs.c_mem, hs.a_le, hs.b_le, hs.c_le, ?_, ?_⟩, hc⟩
  · intro σ hσ
    exact hs.sum_in (σ : G) (Subgroup.mem_subgroupOf.mp hσ)
  · intro σ hσ
    exact hs.sum_out (σ : G) (fun h => hσ (Subgroup.mem_subgroupOf.mpr h))

/- English proof (translation)
The claim follows from `@almostSep_subgroupOf`.
-/
example : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (U H : Subgroup G), AlmostSep v U → AlmostSep v (U.subgroupOf H) := @almostSep_subgroupOf

end GlobalTheory.AlmostEt
