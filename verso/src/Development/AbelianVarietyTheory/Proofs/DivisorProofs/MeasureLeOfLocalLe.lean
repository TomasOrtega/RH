import Mathlib

open MeasureTheory TopologicalSpace

namespace GlobalTheory.FubCover

/- English proof (translation)
Take `⟨T, hT, hU⟩` from `TopologicalSpace.isOpen_iUnion_countable (fun x : W => S x.1) (fun x => hS x.1)`. Rewrite using `[Measure.le_iff]`. Introduce `A hA`. Break down `T.eq_empty_or_nonempty with hTe | hTn` into its components or cases. Establish `hWe : W = ∅`.

Rewrite using `[Set.eq_empty_iff_forall_notMem]`. Introduce `x hxW`. Establish `: x ∈ ⋃ i : W, S i.1` using `Set.mem_iUnion.2 ⟨⟨x, hxW⟩, hx x hxW⟩`. Rewrite `this` using `[← hU, hTe]`. Simplify using `at this`.

Rewrite `hW` using `[hWe, Set.compl_empty]`. Establish `: M A = 0` using `measure_mono_null (Set.subset_univ _) hW`. Rewrite using `[this]`. Conclude with `bot_le`. Take `⟨f, hf⟩` from `hT.exists_eq_range hTn set s : ℕ → Set X := fun n => S (f n).1 with hs`.

Establish `hsm : ∀ n, MeasurableSet (s n)` using `fun n => (hS _).measurableSet`. Establish `hcov : W ⊆ ⋃ n, disjointed s n`. Rewrite using `[iUnion_disjointed]`. Introduce `x hxW`. Establish `: x ∈ ⋃ i : W, S i.1` using `Set.mem_iUnion.2 ⟨⟨x, hxW⟩, hx x hxW⟩`.

Rewrite `this` using `[← hU, hf, Set.biUnion_range]`. Conclude with `this`. Establish `hd : Pairwise (Function.onFun Disjoint fun n => A ∩ disjointed s n)` using `fun i j hij => ((disjoint_disjointed s hij).mono Set.inter_subset_right Set.inter_subset_right)`. Establish `hm : ∀ n, MeasurableSet (A ∩ disjointed s n)` using `fun n => hA.inter (MeasurableSet.disjointed hsm n)`. Combine the equalities or inequalities in the displayed calculation.

Apply `measure_mono` to reduce the goal to its premises. Introduce `x hxA`. Distinguish the cases in `hxW : x ∈ W`. Use `left`. Take `⟨n, hn⟩` from `Set.mem_iUnion.1 (hcov hxW)`.

Conclude with `Set.mem_iUnion.2 ⟨n, hxA, hn⟩`. Use `right`. Conclude with `hxW`. Use `_ ≤ M (⋃ n, A ∩ disjointed s n) + M Wᶜ := measure_union_le _ _`. Use `_ = ∑' n, M (A ∩ disjointed s n) := by rw [hW, add_zero, measure_iUnion hd hm]`.

Use `_ ≤ ∑' n, M' (A ∩ disjointed s n) := ENNReal.tsum_le_tsum fun n => h _ (f n).2 _ (hm n) (Set.inter_subset_right.trans (disjointed_subset s n))`. Use `_ = M' (⋃ n, A ∩ disjointed s n) := (measure_iUnion hd hm).symm`. Use `_ ≤ M' A := measure_mono (Set.iUnion_subset fun n => Set.inter_subset_left)`.
-/
theorem le_of_open_cover (X : Type) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (M M' : Measure X) (S : X → Set X) (W : Set X)
    (hS : ∀ x, IsOpen (S x)) (hx : ∀ x ∈ W, x ∈ S x) (hW : M Wᶜ = 0)
    (h : ∀ x ∈ W, ∀ A : Set X, MeasurableSet A → A ⊆ S x → M A ≤ M' A) : M ≤ M' := by
  obtain ⟨T, hT, hU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x : W => S x.1)
    (fun x => hS x.1)
  rw [Measure.le_iff]
  intro A hA
  rcases T.eq_empty_or_nonempty with hTe | hTn
  · have hWe : W = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hxW
      have : x ∈ ⋃ i : W, S i.1 := Set.mem_iUnion.2 ⟨⟨x, hxW⟩, hx x hxW⟩
      rw [← hU, hTe] at this
      simp at this
    rw [hWe, Set.compl_empty] at hW
    have : M A = 0 := measure_mono_null (Set.subset_univ _) hW
    rw [this]; exact bot_le
  · obtain ⟨f, hf⟩ := hT.exists_eq_range hTn
    set s : ℕ → Set X := fun n => S (f n).1 with hs
    have hsm : ∀ n, MeasurableSet (s n) := fun n => (hS _).measurableSet
    have hcov : W ⊆ ⋃ n, disjointed s n := by
      rw [iUnion_disjointed]
      intro x hxW
      have : x ∈ ⋃ i : W, S i.1 := Set.mem_iUnion.2 ⟨⟨x, hxW⟩, hx x hxW⟩
      rw [← hU, hf, Set.biUnion_range] at this
      exact this
    have hd : Pairwise (Function.onFun Disjoint fun n => A ∩ disjointed s n) :=
      fun i j hij => ((disjoint_disjointed s hij).mono Set.inter_subset_right
        Set.inter_subset_right)
    have hm : ∀ n, MeasurableSet (A ∩ disjointed s n) :=
      fun n => hA.inter (MeasurableSet.disjointed hsm n)
    calc M A ≤ M ((⋃ n, A ∩ disjointed s n) ∪ Wᶜ) := by
          apply measure_mono
          intro x hxA
          by_cases hxW : x ∈ W
          · left
            obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (hcov hxW)
            exact Set.mem_iUnion.2 ⟨n, hxA, hn⟩
          · right; exact hxW
      _ ≤ M (⋃ n, A ∩ disjointed s n) + M Wᶜ := measure_union_le _ _
      _ = ∑' n, M (A ∩ disjointed s n) := by rw [hW, add_zero, measure_iUnion hd hm]
      _ ≤ ∑' n, M' (A ∩ disjointed s n) := ENNReal.tsum_le_tsum fun n =>
          h _ (f n).2 _ (hm n) (Set.inter_subset_right.trans (disjointed_subset s n))
      _ = M' (⋃ n, A ∩ disjointed s n) := (measure_iUnion hd hm).symm
      _ ≤ M' A := measure_mono (Set.iUnion_subset fun n => Set.inter_subset_left)

end GlobalTheory.FubCover
