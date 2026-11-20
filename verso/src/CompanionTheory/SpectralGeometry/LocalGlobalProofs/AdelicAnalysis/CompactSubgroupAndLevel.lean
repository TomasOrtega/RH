import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core

/- English proof (translation)
Use `⟨?_, AddSubgroup.isOpen_mono le_sup_left o₁⟩` and prove the remaining obligations. Rewrite using `[AddSubgroup.add_normal]`. Conclude with `h₁.add h₂`.
-/
theorem compact_open_sup {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    {L₁ L₂ : AddSubgroup V} (h₁ : IsCompact (L₁ : Set V)) (o₁ : IsOpen (L₁ : Set V))
    (h₂ : IsCompact (L₂ : Set V)) :
    IsCompact ((L₁ ⊔ L₂ : AddSubgroup V) : Set V) ∧ IsOpen ((L₁ ⊔ L₂ : AddSubgroup V) : Set V) := by
  refine ⟨?_, AddSubgroup.isOpen_mono le_sup_left o₁⟩
  rw [AddSubgroup.add_normal]
  exact h₁.add h₂

/- English proof (translation)
Introduce `V _ _ _ χ μ h`. Take `⟨hG, hT, -, -, -, -, hnb, hcov, -⟩` from `h`. Use `haveI := hG`. Use `haveI := hT`. Establish `cover : ∀ K : Set V, IsCompact K → ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ K ⊆ L`.

Introduce `K hK`. Use `hK.induction_on (p := fun s => ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ s ⊆ L) ?_ ?_ ?_ ?_` and prove the remaining obligations. Take `⟨L, c, o, -⟩` from `hcov 0`. Conclude with `⟨L, c, o, Set.empty_subset _⟩`. Introduce and unpack `s t hst ⟨L, c, o, hL⟩`.

Conclude with `⟨L, c, o, hst.trans hL⟩`. Introduce and unpack `s t ⟨L₁, c₁, o₁, h₁⟩ ⟨L₂, c₂, o₂, h₂⟩`. Take `⟨c, o⟩` from `compact_open_sup c₁ o₁ c₂`. Use `⟨L₁ ⊔ L₂, c, o, Set.union_subset ?_ ?_⟩` and prove the remaining obligations. Conclude with `h₁.trans (SetLike.coe_subset_coe.2 le_sup_left)`.

Conclude with `h₂.trans (SetLike.coe_subset_coe.2 le_sup_right)`. Introduce `x _`. Take `⟨L, c, o, hx⟩` from `hcov x`. Conclude with `⟨L, mem_nhdsWithin_of_mem_nhds (o.mem_nhds hx), L, c, o, subset_rfl⟩`. Use `⟨cover, ?_⟩` and prove the remaining obligations.

Introduce and unpack `φ ⟨hlc, hcs⟩`. Take `⟨L, c, o, hL⟩` from `cover _ hcs`. Establish `hzero : ∀ x, x ∉ L → φ x = 0` using `fun x hx => image_eq_zero_of_notMem_tsupport (fun hm => hx (hL hm))`. Establish `hg : IsLocallyConstant (fun p : V × V => (φ (p.1 + p.2), φ p.1))` using `(hlc.comp_continuous continuous_add).prodMk (hlc.comp_continuous continuous_fst)`. Establish `hW : IsOpen {p : V × V | φ (p.1 + p.2) = φ p.1}` using `hg {q : ℂ × ℂ | q.1 = q.2}`.

Establish `hsub : (L : Set V) ×ˢ ({0} : Set V) ⊆ {p : V × V | φ (p.1 + p.2) = φ p.1}`. Introduce and unpack `⟨x, y⟩ ⟨-, hy⟩`. Establish `hy' : y = 0` using `hy`. Simplify using `[hy']`. Take `⟨u, v, -, ov, hu, hv, huv⟩` from `generalized_tube_lemma c isCompact_singleton hW hsub`.

Take `⟨L₀, c₀, o₀, h₀⟩` from `hnb v (ov.mem_nhds (hv rfl))`. Use `⟨L, L₀ ⊓ L, c, o, ?_, ?_, inf_le_right, hzero, ?_⟩` and prove the remaining obligations. Use `c₀.inter_right c.isClosed` as an intermediate fact. Simplify using `using this`. Simplify using `using o₀.inter o`.

Introduce `x l hl`. Establish `hl₀ : l ∈ L₀` using `hl.1`. Establish `hlL : l ∈ L` using `hl.2`. Distinguish the cases in `hx : x ∈ L`. Conclude with `huv (Set.mk_mem_prod (hu hx) (h₀ hl₀))`.

Rewrite using `[hzero x hx, hzero _ (fun hm => hx ?_)]`. Simplify using `using L.sub_mem hm hlL`.
-/
theorem compact_subgroup_and_level :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → (∀ K : Set V, IsCompact K → ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ K ⊆ L) ∧ ∀ φ : V → ℂ, SB φ → ∃ L L' : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ IsCompact (L' : Set V) ∧ IsOpen (L' : Set V) ∧ L' ≤ L ∧ (∀ x, x ∉ L → φ x = 0) ∧ ∀ x, ∀ l ∈ L', φ (x + l) = φ x := by
  intro V _ _ _ χ μ h
  obtain ⟨hG, hT, -, -, -, -, hnb, hcov, -⟩ := h
  haveI := hG
  haveI := hT
  have cover : ∀ K : Set V, IsCompact K →
      ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ K ⊆ L := by
    intro K hK
    refine hK.induction_on (p := fun s => ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧
      IsOpen (L : Set V) ∧ s ⊆ L) ?_ ?_ ?_ ?_
    · obtain ⟨L, c, o, -⟩ := hcov 0
      exact ⟨L, c, o, Set.empty_subset _⟩
    · rintro s t hst ⟨L, c, o, hL⟩
      exact ⟨L, c, o, hst.trans hL⟩
    · rintro s t ⟨L₁, c₁, o₁, h₁⟩ ⟨L₂, c₂, o₂, h₂⟩
      obtain ⟨c, o⟩ := compact_open_sup c₁ o₁ c₂
      refine ⟨L₁ ⊔ L₂, c, o, Set.union_subset ?_ ?_⟩
      · exact h₁.trans (SetLike.coe_subset_coe.2 le_sup_left)
      · exact h₂.trans (SetLike.coe_subset_coe.2 le_sup_right)
    · intro x _
      obtain ⟨L, c, o, hx⟩ := hcov x
      exact ⟨L, mem_nhdsWithin_of_mem_nhds (o.mem_nhds hx), L, c, o, subset_rfl⟩
  refine ⟨cover, ?_⟩
  rintro φ ⟨hlc, hcs⟩
  obtain ⟨L, c, o, hL⟩ := cover _ hcs
  have hzero : ∀ x, x ∉ L → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hm => hx (hL hm))
  have hg : IsLocallyConstant (fun p : V × V => (φ (p.1 + p.2), φ p.1)) :=
    (hlc.comp_continuous continuous_add).prodMk (hlc.comp_continuous continuous_fst)
  have hW : IsOpen {p : V × V | φ (p.1 + p.2) = φ p.1} := hg {q : ℂ × ℂ | q.1 = q.2}
  have hsub : (L : Set V) ×ˢ ({0} : Set V) ⊆ {p : V × V | φ (p.1 + p.2) = φ p.1} := by
    rintro ⟨x, y⟩ ⟨-, hy⟩
    have hy' : y = 0 := hy
    simp [hy']
  obtain ⟨u, v, -, ov, hu, hv, huv⟩ := generalized_tube_lemma c isCompact_singleton hW hsub
  obtain ⟨L₀, c₀, o₀, h₀⟩ := hnb v (ov.mem_nhds (hv rfl))
  refine ⟨L, L₀ ⊓ L, c, o, ?_, ?_, inf_le_right, hzero, ?_⟩
  · have := c₀.inter_right c.isClosed
    simpa using this
  · simpa using o₀.inter o
  · intro x l hl
    have hl₀ : l ∈ L₀ := hl.1
    have hlL : l ∈ L := hl.2
    by_cases hx : x ∈ L
    · exact huv (Set.mk_mem_prod (hu hx) (h₀ hl₀))
    · rw [hzero x hx, hzero _ (fun hm => hx ?_)]
      simpa using L.sub_mem hm hlL

end GlobalTheory.CompanionTheory.SW.Core
