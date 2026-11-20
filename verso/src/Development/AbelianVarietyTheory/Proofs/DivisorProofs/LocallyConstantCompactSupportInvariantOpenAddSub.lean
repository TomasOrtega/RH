import Mathlib

namespace GlobalTheory

open Filter Topology

/- English proof (translation)
Introduce `X _ _ _ _ g hg hc`. Establish `key : ∀ z : X, ∃ V : OpenAddSubgroup X, ∀ h ∈ V, g (z + h) = g z`. Introduce `z`. Establish `hT : Tendsto (fun h : X => z + h) (𝓝 0) (𝓝 z)`. Use `(continuous_add_left z).tendsto (0 : X)` as an intermediate fact.

Simplify using `using this`. Establish `hn : {h : X | g (z + h) = g z} ∈ 𝓝 (0 : X)` using `hT.eventually (hg.eventually_eq z)`. Take `⟨V, hV⟩` from `NonarchimedeanAddGroup.is_nonarchimedean _ hn`. Conclude with `⟨V, fun h hh => hV hh⟩`. Use `choose H hH using key`.

Establish `hU : ∀ j y, y - j ∈ H j → g y = g j`. Introduce `j y h`. Use `hH j (y - j) h` as an intermediate fact. Establish `e : j + (y - j) = y` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.

Take `⟨t, ht⟩` from `hc.isCompact.elim_finite_subcover (fun z : X => {y : X | y - z ∈ H z}) (fun z => (H z).isOpen.preimage (continuous_id.sub continuous_const)) (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)`. Use `⟨t.inf H, fun z a ha => ?_⟩` and prove the remaining obligations. Establish `hle : ∀ j ∈ t, a ∈ H j` using `fun j hj => Finset.inf_le (f := H) hj ha`. Distinguish the cases in `hz : z ∈ tsupport g`. Take `⟨j, hj, hzj⟩` from `Set.mem_iUnion₂.1 (ht hz)`.

Establish `h1 : z - j ∈ H j` using `hzj`. Establish `h2 : z + a - j ∈ H j`. Use `(H j).add_mem h1 (hle j hj)` as an intermediate fact. Establish `e : z - j + a = z + a - j` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.

Rewrite using `[hU j _ h2, hU j _ h1]`. Distinguish the cases in `hza : z + a ∈ tsupport g`. Take `⟨j, hj, hzj⟩` from `Set.mem_iUnion₂.1 (ht hza)`. Establish `h1 : z + a - j ∈ H j` using `hzj`. Establish `h2 : z - j ∈ H j`.

Use `(H j).sub_mem h1 (hle j hj)` as an intermediate fact. Establish `e : z + a - j - a = z - j` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Rewrite using `[hU j _ h2, hU j _ h1]`. Rewrite using `[image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hza]`.
-/
theorem locallyConstant_compactSupport_invariant_openAddSubgroup :
    ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
      [NonarchimedeanAddGroup X] (g : X → ℂ), IsLocallyConstant g → HasCompactSupport g →
      ∃ H : OpenAddSubgroup X, ∀ z, ∀ a ∈ H, g (z + a) = g z := by
  intro X _ _ _ _ g hg hc
  have key : ∀ z : X, ∃ V : OpenAddSubgroup X, ∀ h ∈ V, g (z + h) = g z := by
    intro z
    have hT : Tendsto (fun h : X => z + h) (𝓝 0) (𝓝 z) := by
      have := (continuous_add_left z).tendsto (0 : X)
      simpa using this
    have hn : {h : X | g (z + h) = g z} ∈ 𝓝 (0 : X) := hT.eventually (hg.eventually_eq z)
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hn
    exact ⟨V, fun h hh => hV hh⟩
  choose H hH using key
  have hU : ∀ j y, y - j ∈ H j → g y = g j := by
    intro j y h
    have := hH j (y - j) h
    have e : j + (y - j) = y := by abel
    rwa [e] at this
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun z : X => {y : X | y - z ∈ H z})
    (fun z => (H z).isOpen.preimage (continuous_id.sub continuous_const))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
  refine ⟨t.inf H, fun z a ha => ?_⟩
  have hle : ∀ j ∈ t, a ∈ H j := fun j hj => Finset.inf_le (f := H) hj ha
  by_cases hz : z ∈ tsupport g
  · obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.1 (ht hz)
    have h1 : z - j ∈ H j := hzj
    have h2 : z + a - j ∈ H j := by
      have := (H j).add_mem h1 (hle j hj)
      have e : z - j + a = z + a - j := by abel
      rwa [e] at this
    rw [hU j _ h2, hU j _ h1]
  by_cases hza : z + a ∈ tsupport g
  · obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.1 (ht hza)
    have h1 : z + a - j ∈ H j := hzj
    have h2 : z - j ∈ H j := by
      have := (H j).sub_mem h1 (hle j hj)
      have e : z + a - j - a = z - j := by abel
      rwa [e] at this
    rw [hU j _ h2, hU j _ h1]
  rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hza]

end GlobalTheory
