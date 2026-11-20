import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharNegEqOne

open Filter Topology

namespace GlobalTheory.WeilM

/- English proof (translation)
Introduce `f hf`. Take `⟨hlc, hcs⟩` from `hf`. Establish `key : ∀ Y : X, ∃ i, ∀ C ∈ L i, f (Y + C) = f Y`. Introduce `Y`. Establish `h1 : f ⁻¹' {f Y} ∈ 𝓝 (Y + 0)` using `by rw [add_zero]; exact (hlc.isOpen_fiber _).mem_nhds rfl`.

Establish `h2 : {C : X | f (Y + C) = f Y} ∈ 𝓝 (0 : X)` using `(continuous_add_left Y).continuousAt.preimage_mem_nhds h1`. Take `⟨i, hi⟩` from `hb _ h2`. Conclude with `⟨i, fun C hC => hi hC⟩`. Use `choose g hg using key`. Take `⟨t, ht⟩` from `hcs.isCompact.elim_finite_subcover (fun Y => {Z : X | Z - Y ∈ L (g Y)}) (fun Y => (hL _).preimage (continuous_sub_right Y)) (fun Z _ => Set.mem_iUnion.2 ⟨Z, by simp⟩)`.

Establish `hW : (⋂ Y ∈ t, (L (g Y) : Set X)) ∈ 𝓝 (0 : X)` using `(Filter.biInter_finset_mem t).2 fun Y _ => (hL _).mem_nhds (L (g Y)).zero_mem`. Take `⟨j, hj⟩` from `hb _ hW`. Use `⟨j, fun Y C hC => ?_⟩` and prove the remaining obligations. Establish `hCt : ∀ Y0 ∈ t, C ∈ L (g Y0)` using `fun Y0 h0 => by`. Use `hj hC` as an intermediate fact.

Simplify using `only [Set.mem_iInter] at this`. Conclude with `this Y0 h0`. Distinguish the cases in `h : ∃ Y0 ∈ t, Y - Y0 ∈ L (g Y0)`. Take `⟨Y0, h0, hY⟩` from `h`. Establish `e1` using `hg Y0 _ hY`.

Establish `e2` using `hg Y0 _ (add_mem hY (hCt Y0 h0))`. Rewrite `e1` using `[show Y0 + (Y - Y0) = Y by abel]`. Rewrite `e2` using `[show Y0 + (Y - Y0 + C) = Y + C by abel]`. Rewrite using `[e1, e2]`. Use `push_neg at h`.

Establish `hn : ∀ Z, Z ∈ tsupport f → ∃ Y0 ∈ t, Z - Y0 ∈ L (g Y0)` using `fun Z hZ => by`. Use `ht hZ` as an intermediate fact. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq] at this`. Take `⟨Y0, h0, h1⟩` from `this`. Conclude with `⟨Y0, h0, h1⟩`.

Establish `hY : Y ∉ tsupport f` using `fun hZ => by`. Take `⟨Y0, h0, h1⟩` from `hn Y hZ`. Conclude with `h Y0 h0 h1`. Establish `hYC : Y + C ∉ tsupport f` using `fun hZ => by`. Take `⟨Y0, h0, h1⟩` from `hn _ hZ`.

Apply `h Y0 h0` to reduce the goal to its premises. Use `sub_mem h1 (hCt Y0 h0)` as an intermediate fact. Rewrite `this` using `[show Y + C - Y0 - C = Y - Y0 by abel]`. Then use the resulting hypothesis. Rewrite using `[image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hYC]`.
-/
theorem SB.exists_periodic {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] {ι : Type}
    (L : ι → AddSubgroup X) (hL : ∀ i, IsOpen (L i : Set X)) (hb : ∀ W ∈ 𝓝 (0 : X), ∃ i, (L i : Set X) ⊆ W) :
    ∀ f ∈ GlobalTheory.WeilM.SB X, ∃ i, ∀ Y, ∀ C ∈ L i, f (Y + C) = f Y := by
  intro f hf
  obtain ⟨hlc, hcs⟩ := hf
  have key : ∀ Y : X, ∃ i, ∀ C ∈ L i, f (Y + C) = f Y := by
    intro Y
    have h1 : f ⁻¹' {f Y} ∈ 𝓝 (Y + 0) := by rw [add_zero]; exact (hlc.isOpen_fiber _).mem_nhds rfl
    have h2 : {C : X | f (Y + C) = f Y} ∈ 𝓝 (0 : X) := (continuous_add_left Y).continuousAt.preimage_mem_nhds h1
    obtain ⟨i, hi⟩ := hb _ h2
    exact ⟨i, fun C hC => hi hC⟩
  choose g hg using key
  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover (fun Y => {Z : X | Z - Y ∈ L (g Y)})
    (fun Y => (hL _).preimage (continuous_sub_right Y))
    (fun Z _ => Set.mem_iUnion.2 ⟨Z, by simp⟩)
  have hW : (⋂ Y ∈ t, (L (g Y) : Set X)) ∈ 𝓝 (0 : X) :=
    (Filter.biInter_finset_mem t).2 fun Y _ => (hL _).mem_nhds (L (g Y)).zero_mem
  obtain ⟨j, hj⟩ := hb _ hW
  refine ⟨j, fun Y C hC => ?_⟩
  have hCt : ∀ Y0 ∈ t, C ∈ L (g Y0) := fun Y0 h0 => by
    have := hj hC
    simp only [Set.mem_iInter] at this
    exact this Y0 h0
  by_cases h : ∃ Y0 ∈ t, Y - Y0 ∈ L (g Y0)
  · obtain ⟨Y0, h0, hY⟩ := h
    have e1 := hg Y0 _ hY
    have e2 := hg Y0 _ (add_mem hY (hCt Y0 h0))
    rw [show Y0 + (Y - Y0) = Y by abel] at e1
    rw [show Y0 + (Y - Y0 + C) = Y + C by abel] at e2
    rw [e1, e2]
  · push_neg at h
    have hn : ∀ Z, Z ∈ tsupport f → ∃ Y0 ∈ t, Z - Y0 ∈ L (g Y0) := fun Z hZ => by
      have := ht hZ
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
      obtain ⟨Y0, h0, h1⟩ := this
      exact ⟨Y0, h0, h1⟩
    have hY : Y ∉ tsupport f := fun hZ => by
      obtain ⟨Y0, h0, h1⟩ := hn Y hZ
      exact h Y0 h0 h1
    have hYC : Y + C ∉ tsupport f := fun hZ => by
      obtain ⟨Y0, h0, h1⟩ := hn _ hZ
      apply h Y0 h0
      have := sub_mem h1 (hCt Y0 h0)
      rwa [show Y + C - Y0 - C = Y - Y0 by abel] at this
    rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hYC]

end GlobalTheory.WeilM
