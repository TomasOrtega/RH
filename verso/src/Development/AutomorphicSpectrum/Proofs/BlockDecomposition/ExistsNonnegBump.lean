import Mathlib

open Topology

namespace GlobalTheory.CompanionTheory.Bump

/- English proof (translation)
Introduce `X _ _ _ x N hN`. Establish `hx : x ∈ interior N` using `mem_interior_iff_mem_nhds.mpr hN`. Take `⟨f, hf1, hf0, hfc, hfI⟩` from `exists_continuous_one_zero_of_isCompact (s := {x}) (t := (interior N)ᶜ) isCompact_singleton isOpen_interior.isClosed_compl (Set.disjoint_singleton_left.mpr (fun h => h hx))`. Use `⟨f, f.continuous, hfc, fun y => (hfI y).1, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : f x = 1` using `hf1 (Set.mem_singleton x)`.

Rewrite using `[h1]`. Conclude with `one_ne_zero`. Introduce `y hy`. Assume the negation of the conclusion as `hyN`. Conclude with `hy (hf0 (fun hi => hyN (interior_subset hi)))`.
-/
theorem exists_nonneg_bump :
    ∀ {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] (x : X) (N : Set X),
      N ∈ 𝓝 x → ∃ φ : X → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ 0 ≤ φ ∧ φ x ≠ 0 ∧
        Function.support φ ⊆ N := by
  intro X _ _ _ x N hN
  have hx : x ∈ interior N := mem_interior_iff_mem_nhds.mpr hN
  obtain ⟨f, hf1, hf0, hfc, hfI⟩ := exists_continuous_one_zero_of_isCompact
    (s := {x}) (t := (interior N)ᶜ) isCompact_singleton isOpen_interior.isClosed_compl
    (Set.disjoint_singleton_left.mpr (fun h => h hx))
  refine ⟨f, f.continuous, hfc, fun y => (hfI y).1, ?_, ?_⟩
  · have h1 : f x = 1 := hf1 (Set.mem_singleton x)
    rw [h1]
    exact one_ne_zero
  · intro y hy
    by_contra hyN
    exact hy (hf0 (fun hi => hyN (interior_subset hi)))

end GlobalTheory.CompanionTheory.Bump
