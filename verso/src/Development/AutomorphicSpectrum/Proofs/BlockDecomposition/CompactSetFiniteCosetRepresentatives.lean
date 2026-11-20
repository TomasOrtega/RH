import Mathlib
open scoped Topology

namespace GlobalTheory.CompanionTheory.OpenSubgroupCosets

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_finset_unique_coset_reps :
    ∀ {E : Type} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
      (D : AddSubgroup E), IsOpen (D : Set E) → ∀ (R : Set E), IsCompact R →
      ∃ S : Finset E, (∀ s ∈ S, s ∈ R) ∧ ∀ x ∈ R, ∃! s, s ∈ S ∧ x - s ∈ D := by
  intro E _ _ _ D hD R hR
  classical
  obtain ⟨t, ht⟩ := hR.elim_finite_subcover (fun x : E => (fun y => y - x) ⁻¹' (D : Set E))
    (fun x => hD.preimage (continuous_sub_right x))
    (fun r _ => Set.mem_iUnion.2 ⟨r, by simp⟩)
  set π : E → E ⧸ D := QuotientAddGroup.mk with hπ
  have hfin : (π '' R).Finite := by
    apply (t.finite_toSet.image π).subset
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨x, hx, hrx⟩ : ∃ x ∈ t, r - x ∈ D := by simpa using ht hr
    refine ⟨x, hx, ?_⟩
    apply QuotientAddGroup.eq_iff_sub_mem.2
    rw [← neg_sub]
    exact D.neg_mem hrx
  have hrep : ∀ c ∈ π '' R, ∃ r, r ∈ R ∧ π r = c := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨r, hr, rfl⟩
  choose! f hfR hfπ using hrep
  refine ⟨hfin.toFinset.image f, ?_, ?_⟩
  · intro s hs
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hs
    exact hfR c (hfin.mem_toFinset.1 hc)
  · intro x hx
    have hxc : π x ∈ π '' R := ⟨x, hx, rfl⟩
    refine ⟨f (π x), ⟨Finset.mem_image.2 ⟨π x, hfin.mem_toFinset.2 hxc, rfl⟩, ?_⟩, ?_⟩
    · exact QuotientAddGroup.eq_iff_sub_mem.1 (hfπ (π x) hxc).symm
    · rintro s ⟨hs, hxs⟩
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hs
      have hc' := hfin.mem_toFinset.1 hc
      have h1 : π x = c := by
        rw [← hfπ c hc']
        exact QuotientAddGroup.eq_iff_sub_mem.2 hxs
      rw [h1]

end GlobalTheory.CompanionTheory.OpenSubgroupCosets
