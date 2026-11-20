import Mathlib

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

/- English proof (translation)
Introduce `G _ _ _ _ _ _ V _ _ _ a ha h1 hmul Z x hZ hZx Ω hΩ`. Establish `hmem : ∀ (g : G) (z : Z), a g z ∈ Z`. Introduce `g z`. Take `⟨h, hh⟩` from `(hZx z).1 z.2`. Conclude with `(hZx _).2 ⟨g * h, by rw [hmul, hh]⟩`.

Use `letI : MulAction G Z := { smul := fun g z => ⟨a g z, hmem g z⟩ one_smul := fun z => Subtype.ext (h1 z) mul_smul := fun g h z => Subtype.ext (hmul g h z) }`. Use `haveI : ContinuousSMul G Z := ⟨Continuous.subtype_mk (ha.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) (fun p => hmem p.1 p.2)⟩`. Use `haveI : MulAction.IsPretransitive G Z := by`. Use `⟨fun z w => ?_⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `(hZx z).1 z.2`.

Take `⟨h, hh⟩` from `(hZx w).1 w.2`. Use `⟨h * g⁻¹, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show a (h * g⁻¹) z = w`. Rewrite using `[← hg, ← hmul, inv_mul_cancel_right, hh]`. Use `haveI : LocallyCompactSpace Z := hZ.locallyCompactSpace`.

Use `haveI : BaireSpace Z := BaireSpace.of_t2Space_locallyCompactSpace`. Establish `hx : x ∈ Z` using `(hZx x).2 ⟨1, h1 x⟩`. Establish `hopen` using `isOpenMap_smul_of_sigmaCompact (G := G) (X := Z) ⟨x, hx⟩`. Use `choose K hK hKn using fun g : G => exists_compact_mem_nhds g`. Establish `hS : IsCompact ((Subtype.val : Z → V) ⁻¹' Ω)` using `hZ.isClosedEmbedding_subtypeVal.isCompact_preimage hΩ`.

Take `⟨t, ht⟩` from `hS.elim_finite_subcover (fun g => (fun h : G => h • (⟨x, hx⟩ : Z)) '' interior (K g)) (fun g => hopen _ isOpen_interior) (by`. Introduce `z _`. Take `⟨g, hg⟩` from `(hZx z).1 z.2`. Conclude with `Set.mem_iUnion.2 ⟨g, g, mem_interior_iff_mem_nhds.2 (hKn g), Subtype.ext hg⟩)`. Use `⟨⋃ g ∈ t, K g, t.isCompact_biUnion fun g _ => hK g, ?_⟩` and prove the remaining obligations.

Introduce `y hyΩ hyZ`. Establish `hy` using `ht (show (⟨y, hyZ⟩ : Z) ∈ (Subtype.val : Z → V) ⁻¹' Ω from hyΩ)`. Rewrite `hy` using `[Set.mem_iUnion₂]`. Take `⟨g, hgt, c, hc, hcy⟩` from `hy`. Conclude with `⟨c, Set.mem_biUnion hgt (interior_subset hc), congrArg Subtype.val hcy⟩`.
-/
theorem compact_part_closed_orbit :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [SecondCountableTopology G] (V : Type) [TopologicalSpace V]
      [T2Space V] [LocallyCompactSpace V] (a : G → V → V),
      (Continuous fun p : G × V => a p.1 p.2) → (∀ y, a 1 y = y) →
      (∀ g h y, a (g * h) y = a g (a h y)) →
      ∀ (Z : Set V) (x : V), IsClosed Z → (∀ y, y ∈ Z ↔ ∃ g, a g x = y) →
      ∀ Ω : Set V, IsCompact Ω → ∃ C : Set G, IsCompact C ∧ ∀ y ∈ Ω, y ∈ Z → ∃ c ∈ C, a c x = y := by
  intro G _ _ _ _ _ _ V _ _ _ a ha h1 hmul Z x hZ hZx Ω hΩ
  have hmem : ∀ (g : G) (z : Z), a g z ∈ Z := by
    intro g z
    obtain ⟨h, hh⟩ := (hZx z).1 z.2
    exact (hZx _).2 ⟨g * h, by rw [hmul, hh]⟩
  letI : MulAction G Z :=
    { smul := fun g z => ⟨a g z, hmem g z⟩
      one_smul := fun z => Subtype.ext (h1 z)
      mul_smul := fun g h z => Subtype.ext (hmul g h z) }
  haveI : ContinuousSMul G Z :=
    ⟨Continuous.subtype_mk
      (ha.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
      (fun p => hmem p.1 p.2)⟩
  haveI : MulAction.IsPretransitive G Z := by
    refine ⟨fun z w => ?_⟩
    obtain ⟨g, hg⟩ := (hZx z).1 z.2
    obtain ⟨h, hh⟩ := (hZx w).1 w.2
    refine ⟨h * g⁻¹, Subtype.ext ?_⟩
    show a (h * g⁻¹) z = w
    rw [← hg, ← hmul, inv_mul_cancel_right, hh]
  haveI : LocallyCompactSpace Z := hZ.locallyCompactSpace
  haveI : BaireSpace Z := BaireSpace.of_t2Space_locallyCompactSpace
  have hx : x ∈ Z := (hZx x).2 ⟨1, h1 x⟩
  have hopen := isOpenMap_smul_of_sigmaCompact (G := G) (X := Z) ⟨x, hx⟩
  choose K hK hKn using fun g : G => exists_compact_mem_nhds g
  have hS : IsCompact ((Subtype.val : Z → V) ⁻¹' Ω) :=
    hZ.isClosedEmbedding_subtypeVal.isCompact_preimage hΩ
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun g => (fun h : G => h • (⟨x, hx⟩ : Z)) '' interior (K g))
    (fun g => hopen _ isOpen_interior) (by
      intro z _
      obtain ⟨g, hg⟩ := (hZx z).1 z.2
      exact Set.mem_iUnion.2 ⟨g, g, mem_interior_iff_mem_nhds.2 (hKn g), Subtype.ext hg⟩)
  refine ⟨⋃ g ∈ t, K g, t.isCompact_biUnion fun g _ => hK g, ?_⟩
  intro y hyΩ hyZ
  have hy := ht (show (⟨y, hyZ⟩ : Z) ∈ (Subtype.val : Z → V) ⁻¹' Ω from hyΩ)
  rw [Set.mem_iUnion₂] at hy
  obtain ⟨g, hgt, c, hc, hcy⟩ := hy
  exact ⟨c, Set.mem_biUnion hgt (interior_subset hc), congrArg Subtype.val hcy⟩

end GlobalTheory.CompanionTheory.Adelic
