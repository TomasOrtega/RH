import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

namespace GlobalTheory.RootEx

open MeasureTheory ValuativeRel Matrix in
open scoped Topology Pointwise in

/- English proof (translation)
Take `⟨t, ht⟩` from `hcs.elim_finite_subcover (fun c : ℂ => {x | Φ x = c}) (fun c => hlc.isOpen_fiber c) (fun x _ => Set.mem_iUnion.2 ⟨Φ x, rfl⟩)`. Establish `hV : ∀ c : ℂ, ∃ V ∈ 𝓝 (0 : X), c ≠ 0 → {x | Φ x = c} + V ⊆ {x | Φ x = c}`. Introduce `c`. Distinguish the cases in `hc : c = 0`. Conclude with `⟨Set.univ, Filter.univ_mem, fun h => (h hc).elim⟩`.

Establish `hsub : {x | Φ x = c} ⊆ tsupport Φ` using `fun x hx => subset_tsupport Φ (by`. Rewrite using `[Function.mem_support]`. Rewrite `hx` using `[Set.mem_setOf_eq]`. Rewrite using `[hx]`. Conclude with `hc)`.

Take `⟨V, hV0, hVs⟩` from `compact_open_separated_add_right (hcs.of_isClosed_subset (hlc.isClosed_fiber c) hsub) (hlc.isOpen_fiber c) le_rfl`. Conclude with `⟨V, hV0, fun _ => hVs⟩`. Use `choose V hV0 hVsub using hV`. Establish `hW : (⋂ c ∈ t, (V c ∩ -V c)) ∈ 𝓝 (0 : X)` using `(Filter.biInter_finset_mem t).2 fun c _ => Filter.inter_mem (hV0 c) (neg_mem_nhds_zero X (hV0 c))`. Establish `hstep : ∀ x, ∀ v ∈ (⋂ c ∈ t, (V c ∩ -V c)), Φ (x + v) = Φ x`.

Introduce `x v hv`. Establish `hv' : ∀ c ∈ t, v ∈ V c ∧ -v ∈ V c`. Introduce `c hc`. Establish `h` using `Set.mem_iInter₂.1 hv c hc`. Conclude with `⟨h.1, Set.mem_neg.1 h.2⟩`.

Distinguish the cases in `h0 : Φ x = 0`. Assume the negation of the conclusion as `hne`. Establish `hne' : Φ (x + v) ≠ 0` using `by rwa [h0] at hne`. Establish `hxK : x + v ∈ tsupport Φ` using `subset_tsupport Φ hne'`. Take `⟨c, hct, hc⟩` from `Set.mem_iUnion₂.1 (ht hxK)`.

Establish `hc' : Φ (x + v) = c` using `hc`. Establish `hc0 : c ≠ 0` using `hc' ▸ hne'`. Establish `h` using `hVsub c hc0 (Set.add_mem_add hc (hv' c hct).2)`. Establish `h' : Φ (x + v + -v) = c` using `h`. Rewrite `h'` using `[add_neg_cancel_right]`.

Conclude with `hc0 (h'.symm.trans h0)`. Establish `hxK : x ∈ tsupport Φ` using `subset_tsupport Φ h0`. Take `⟨c, hct, hc⟩` from `Set.mem_iUnion₂.1 (ht hxK)`. Establish `hc' : Φ x = c` using `hc`. Establish `hc0 : c ≠ 0` using `hc' ▸ h0`.

Establish `h` using `hVsub c hc0 (Set.add_mem_add hc (hv' c hct).1)`. Establish `h' : Φ (x + v) = c` using `h`. Conclude with `h'.trans hc'.symm`. Use `⟨AddSubgroup.closure (⋂ c ∈ t, (V c ∩ -V c)), AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (Filter.mem_of_superset hW AddSubgroup.subset_closure), ?_⟩` and prove the remaining obligations. Introduce `x y hy`.

Proceed by induction on `hy using AddSubgroup.closure_induction generalizing x with`. Consider the case `mem y hy => exact hstep x y hy`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [← add_assoc, hz, hy]`. Consider the case `neg y _ hy`.

Establish `h` using `hy (x + -y)`. Rewrite `h` using `[neg_add_cancel_right]`. Conclude with `h.symm`.
-/
theorem _root_.GlobalTheory.RootEx.exists_isOpen_addSubgroup_add_eq {X : Type*}
    [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] {Φ : X → ℂ} (hlc : IsLocallyConstant Φ) (hcs : IsCompact (tsupport Φ)) :
    ∃ Λ : AddSubgroup X, IsOpen (Λ : Set X) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  classical
  obtain ⟨t, ht⟩ := hcs.elim_finite_subcover (fun c : ℂ => {x | Φ x = c})
    (fun c => hlc.isOpen_fiber c) (fun x _ => Set.mem_iUnion.2 ⟨Φ x, rfl⟩)
  have hV : ∀ c : ℂ, ∃ V ∈ 𝓝 (0 : X), c ≠ 0 → {x | Φ x = c} + V ⊆ {x | Φ x = c} := by
    intro c
    by_cases hc : c = 0
    · exact ⟨Set.univ, Filter.univ_mem, fun h => (h hc).elim⟩
    · have hsub : {x | Φ x = c} ⊆ tsupport Φ := fun x hx =>
        subset_tsupport Φ (by
          rw [Function.mem_support]
          rw [Set.mem_setOf_eq] at hx
          rw [hx]
          exact hc)
      obtain ⟨V, hV0, hVs⟩ := compact_open_separated_add_right
        (hcs.of_isClosed_subset (hlc.isClosed_fiber c) hsub) (hlc.isOpen_fiber c) le_rfl
      exact ⟨V, hV0, fun _ => hVs⟩
  choose V hV0 hVsub using hV
  have hW : (⋂ c ∈ t, (V c ∩ -V c)) ∈ 𝓝 (0 : X) :=
    (Filter.biInter_finset_mem t).2 fun c _ =>
      Filter.inter_mem (hV0 c) (neg_mem_nhds_zero X (hV0 c))
  have hstep : ∀ x, ∀ v ∈ (⋂ c ∈ t, (V c ∩ -V c)), Φ (x + v) = Φ x := by
    intro x v hv
    have hv' : ∀ c ∈ t, v ∈ V c ∧ -v ∈ V c := by
      intro c hc
      have h := Set.mem_iInter₂.1 hv c hc
      exact ⟨h.1, Set.mem_neg.1 h.2⟩
    by_cases h0 : Φ x = 0
    · by_contra hne
      have hne' : Φ (x + v) ≠ 0 := by rwa [h0] at hne
      have hxK : x + v ∈ tsupport Φ := subset_tsupport Φ hne'
      obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hxK)
      have hc' : Φ (x + v) = c := hc
      have hc0 : c ≠ 0 := hc' ▸ hne'
      have h := hVsub c hc0 (Set.add_mem_add hc (hv' c hct).2)
      have h' : Φ (x + v + -v) = c := h
      rw [add_neg_cancel_right] at h'
      exact hc0 (h'.symm.trans h0)
    · have hxK : x ∈ tsupport Φ := subset_tsupport Φ h0
      obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hxK)
      have hc' : Φ x = c := hc
      have hc0 : c ≠ 0 := hc' ▸ h0
      have h := hVsub c hc0 (Set.add_mem_add hc (hv' c hct).1)
      have h' : Φ (x + v) = c := h
      exact h'.trans hc'.symm
  refine ⟨AddSubgroup.closure (⋂ c ∈ t, (V c ∩ -V c)),
    AddSubgroup.isOpen_of_mem_nhds _ (g := 0)
      (Filter.mem_of_superset hW AddSubgroup.subset_closure), ?_⟩
  intro x y hy
  induction hy using AddSubgroup.closure_induction generalizing x with
  | mem y hy => exact hstep x y hy
  | zero => simp
  | add y z _ _ hy hz => rw [← add_assoc, hz, hy]
  | neg y _ hy =>
    have h := hy (x + -y)
    rw [neg_add_cancel_right] at h
    exact h.symm

open MeasureTheory ValuativeRel Matrix in
open scoped Topology Pointwise in

/- English proof (translation)
Introduce `k _ _ _ _ a b _ _ Φ hΦ`. Take `⟨hlc, hcs⟩` from `hΦ`. Conclude with `_root_.GlobalTheory.RootEx.exists_isOpen_addSubgroup_add_eq hlc hcs`.
-/
theorem _root_.GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (a b : Type) [Fintype a] [Fintype b], ∀ Φ ∈ _root_.GlobalTheory.SplitWeil.SB (Matrix a b k),
      ∃ Λ : AddSubgroup (Matrix a b k), IsOpen (Λ : Set (Matrix a b k)) ∧
        ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  intro k _ _ _ _ a b _ _ Φ hΦ
  obtain ⟨hlc, hcs⟩ := hΦ
  exact _root_.GlobalTheory.RootEx.exists_isOpen_addSubgroup_add_eq hlc hcs

end GlobalTheory.RootEx
