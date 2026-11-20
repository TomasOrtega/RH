import Mathlib
open Matrix

namespace GlobalTheory.CompanionTheory.Topology

/- English proof (translation)
Establish `hcoset : ∀ x : X, ((↑) : X → X ⧸ L) '' (Homeomorph.addLeft x '' (L : Set X)) = {(x : X ⧸ L)}`. Introduce `x`. Use extensionality with `q`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨l, hl, rfl⟩, rfl⟩`.

Rewrite using `[Set.mem_singleton_iff, QuotientAddGroup.eq, Homeomorph.coe_addLeft]`. Simplify using `using L.neg_mem hl`. Introduce and unpack `rfl`. Conclude with `⟨x, ⟨0, L.zero_mem, by simp⟩, rfl⟩`. Establish `hdisc : DiscreteTopology (X ⧸ L)`.

Rewrite using `[discreteTopology_iff_isOpen_singleton]`. Introduce `q`. Proceed by induction on `q using QuotientAddGroup.induction_on with`. Consider the case `H x`. Rewrite using `[← hcoset x]`.

Conclude with `QuotientAddGroup.isOpenMap_coe _ ((Homeomorph.addLeft x).isOpenMap _ hL)`. Establish `hfin : (((↑) : X → X ⧸ L) '' (A : Set X)).Finite` using `(hA.image continuous_quotient_mk').finite_of_discrete`. Establish `hout : ∀ q : X ⧸ L, ((q.out : X) : X ⧸ L) = q` using `fun q => Quotient.out_eq q`. Use `⟨hfin.toFinset.image Quotient.out, ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`.

Simplify using `only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_image] at ht`. Take `⟨_, ⟨a, ha, rfl⟩, rfl⟩` from `ht`. Establish `h1 : -(a : X ⧸ L).out + a ∈ L` using `QuotientAddGroup.eq.1 (hout _)`. Establish `h2 : (a : X ⧸ L).out = a - (-(a : X ⧸ L).out + a)` using `by abel`. Rewrite using `[h2]`.

Conclude with `A.sub_mem ha (_hLA h1)`. Introduce `a ha`. Establish `hmem : (a : X ⧸ L).out ∈ hfin.toFinset.image Quotient.out` using `Finset.mem_image.2 ⟨(a : X ⧸ L), (Set.Finite.mem_toFinset hfin).2 ⟨a, ha, rfl⟩, rfl⟩`. Establish `hrel : -(a : X ⧸ L).out + a ∈ L` using `QuotientAddGroup.eq.1 (hout _)`. Use `⟨(a : X ⧸ L).out, ⟨hmem, by rw [sub_eq_neg_add]; exact hrel⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `t' ⟨ht', hat'⟩`. Simplify using `only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_image] at ht'`. Take `⟨q', -, rfl⟩` from `ht'`. Establish `hq : q' = (a : X ⧸ L)`. Rewrite using `[← hout q', QuotientAddGroup.eq]`.

Rewrite `hat'` using `[sub_eq_neg_add]`. Conclude with `hat'`. Rewrite using `[hq]`.
-/
theorem exists_finset_transversal_of_isCompact_of_isOpen
    (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (A L : AddSubgroup X) (hA : IsCompact (A : Set X)) (hL : IsOpen (L : Set X)) (_hLA : L ≤ A) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L) := by
  classical
  have hcoset : ∀ x : X, ((↑) : X → X ⧸ L) '' (Homeomorph.addLeft x '' (L : Set X)) =
      {(x : X ⧸ L)} := by
    intro x
    ext q
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      rw [Set.mem_singleton_iff, QuotientAddGroup.eq, Homeomorph.coe_addLeft]
      simpa using L.neg_mem hl
    · rintro rfl
      exact ⟨x, ⟨0, L.zero_mem, by simp⟩, rfl⟩
  have hdisc : DiscreteTopology (X ⧸ L) := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      rw [← hcoset x]
      exact QuotientAddGroup.isOpenMap_coe _ ((Homeomorph.addLeft x).isOpenMap _ hL)
  have hfin : (((↑) : X → X ⧸ L) '' (A : Set X)).Finite :=
    (hA.image continuous_quotient_mk').finite_of_discrete
  have hout : ∀ q : X ⧸ L, ((q.out : X) : X ⧸ L) = q := fun q => Quotient.out_eq q
  refine ⟨hfin.toFinset.image Quotient.out, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_image] at ht
    obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := ht
    have h1 : -(a : X ⧸ L).out + a ∈ L := QuotientAddGroup.eq.1 (hout _)
    have h2 : (a : X ⧸ L).out = a - (-(a : X ⧸ L).out + a) := by abel
    rw [h2]
    exact A.sub_mem ha (_hLA h1)
  · intro a ha
    have hmem : (a : X ⧸ L).out ∈ hfin.toFinset.image Quotient.out :=
      Finset.mem_image.2 ⟨(a : X ⧸ L), (Set.Finite.mem_toFinset hfin).2 ⟨a, ha, rfl⟩, rfl⟩
    have hrel : -(a : X ⧸ L).out + a ∈ L := QuotientAddGroup.eq.1 (hout _)
    refine ⟨(a : X ⧸ L).out, ⟨hmem, by rw [sub_eq_neg_add]; exact hrel⟩, ?_⟩
    rintro t' ⟨ht', hat'⟩
    simp only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_image] at ht'
    obtain ⟨q', -, rfl⟩ := ht'
    have hq : q' = (a : X ⧸ L) := by
      rw [← hout q', QuotientAddGroup.eq]
      rw [sub_eq_neg_add] at hat'
      exact hat'
    rw [hq]

end GlobalTheory.CompanionTheory.Topology
