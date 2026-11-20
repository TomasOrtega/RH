import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt
open Filter GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.BCT

/- English proof (translation)
Introduce `hp hcof hcpt hKH hT hcomm x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hle : cptPart T ≤ T ⊓ ⨅ i, (cptPart (TH i)).comap (p i)`. Rewrite using `[cptPart, Subgroup.closure_le]`.

Introduce `t ht`. Take `⟨htT, htc⟩` from `ht`. Rewrite using `[SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_iInf]`. Use `⟨htT, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.mem_comap]`.

Use `Subgroup.subset_closure (k := {s | s ∈ TH i ∧ IsCompact (closure (Subgroup.zpowers s : Set (H i)))}) ⟨(hT t).1 htT i, ?_⟩` and prove the remaining obligations. Establish `himc : IsCompact (p i '' closure (Subgroup.zpowers t : Set G))` using `htc.image (hp i)`. Use `himc.of_isClosed_subset isClosed_closure (closure_minimal ?_ himc.isClosed)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩`.

Use `hle hx` as an intermediate fact. Simplify using `only [Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap] at this`. Conclude with `this`. Introduce and unpack `⟨hxT, hxi⟩`. Establish `hloc : ∀ i, IsCompact (closure (Subgroup.zpowers (p i x) : Set (H i)))` using `fun i => (GlobalTheory.LocFinU.cptPart_subset_of_comm (TH i) (hcomm i) (hxi i)).2`.

Use `set C : ∀ i, Set (H i) := fun i => if p i x ∈ KH i then (KH i : Set (H i)) else closure (Subgroup.zpowers (p i x) : Set (H i)) with hC`. Establish `hCc : ∀ i, IsCompact (C i)`. Introduce `i`. Simplify using `only [hC]`. Use `split_ifs`.

Conclude with `hKH i`. Conclude with `hloc i`. Establish `hCf : ∀ᶠ i in cofinite, C i = KH i` using `by filter_upwards [hcof x] with i hi`. Simplify using `[hC, hi]`. Establish `hS` using `hcpt C hCc hCf`.

Establish `hScl : IsClosed {y : G | ∀ i, p i y ∈ C i}`. Establish `: {y : G | ∀ i, p i y ∈ C i} = ⋂ i, p i ⁻¹' C i` using `by ext; simp`. Rewrite using `[this]`. Conclude with `isClosed_iInter fun i => (hCc i).isClosed.preimage (hp i)`. Establish `hsub : (Subgroup.zpowers x : Set G) ⊆ {y : G | ∀ i, p i y ∈ C i}`.

Introduce and unpack `_ ⟨k, rfl⟩ i`. Simplify using `only [hC, map_zpow]`. Use `split_ifs with h`. Conclude with `(KH i).zpow_mem h k`. Conclude with `subset_closure ⟨k, rfl⟩`.

Use `Subgroup.subset_closure (k := {s | s ∈ T ∧ IsCompact (closure (Subgroup.zpowers s : Set G))}) ⟨hxT, ?_⟩` and prove the remaining obligations. Conclude with `hS.of_isClosed_subset isClosed_closure (closure_minimal hsub hScl)`.
-/
theorem mem_cptPart_iff_local (ι G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : ι → Type)
    [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, T2Space (H i)]
    (p : ∀ i, G →* H i) (KH : ∀ i, Subgroup (H i)) (T : Subgroup G) (TH : ∀ i, Subgroup (H i)) :
    (∀ i, Continuous (p i)) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) →
    (∀ C : ∀ i, Set (H i), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = KH i) →
      IsCompact {x : G | ∀ i, p i x ∈ C i}) →
    (∀ i, IsCompact (KH i : Set (H i))) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) →
    (∀ i, ∀ a ∈ TH i, ∀ b ∈ TH i, a * b = b * a) →
    ∀ x, x ∈ cptPart T ↔ x ∈ T ∧ ∀ i, p i x ∈ cptPart (TH i) := by
  intro hp hcof hcpt hKH hT hcomm x
  constructor
  · intro hx
    have hle : cptPart T ≤ T ⊓ ⨅ i, (cptPart (TH i)).comap (p i) := by
      rw [cptPart, Subgroup.closure_le]
      intro t ht
      obtain ⟨htT, htc⟩ := ht
      rw [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_iInf]
      refine ⟨htT, fun i => ?_⟩
      rw [Subgroup.mem_comap]
      refine Subgroup.subset_closure (k := {s | s ∈ TH i ∧ IsCompact (closure (Subgroup.zpowers s : Set (H i)))})
        ⟨(hT t).1 htT i, ?_⟩
      have himc : IsCompact (p i '' closure (Subgroup.zpowers t : Set G)) := htc.image (hp i)
      refine himc.of_isClosed_subset isClosed_closure (closure_minimal ?_ himc.isClosed)
      rintro _ ⟨k, rfl⟩
      exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
    have := hle hx
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap] at this
    exact this
  · rintro ⟨hxT, hxi⟩
    have hloc : ∀ i, IsCompact (closure (Subgroup.zpowers (p i x) : Set (H i))) := fun i =>
      (GlobalTheory.LocFinU.cptPart_subset_of_comm (TH i) (hcomm i) (hxi i)).2
    set C : ∀ i, Set (H i) := fun i => if p i x ∈ KH i then (KH i : Set (H i))
      else closure (Subgroup.zpowers (p i x) : Set (H i)) with hC
    have hCc : ∀ i, IsCompact (C i) := by
      intro i
      simp only [hC]
      split_ifs
      · exact hKH i
      · exact hloc i
    have hCf : ∀ᶠ i in cofinite, C i = KH i := by
      filter_upwards [hcof x] with i hi
      simp [hC, hi]
    have hS := hcpt C hCc hCf
    have hScl : IsClosed {y : G | ∀ i, p i y ∈ C i} := by
      have : {y : G | ∀ i, p i y ∈ C i} = ⋂ i, p i ⁻¹' C i := by ext; simp
      rw [this]
      exact isClosed_iInter fun i => (hCc i).isClosed.preimage (hp i)
    have hsub : (Subgroup.zpowers x : Set G) ⊆ {y : G | ∀ i, p i y ∈ C i} := by
      rintro _ ⟨k, rfl⟩ i
      simp only [hC, map_zpow]
      split_ifs with h
      · exact (KH i).zpow_mem h k
      · exact subset_closure ⟨k, rfl⟩
    refine Subgroup.subset_closure (k := {s | s ∈ T ∧ IsCompact (closure (Subgroup.zpowers s : Set G))}) ⟨hxT, ?_⟩
    exact hS.of_isClosed_subset isClosed_closure (closure_minimal hsub hScl)

end GlobalTheory.BCT
