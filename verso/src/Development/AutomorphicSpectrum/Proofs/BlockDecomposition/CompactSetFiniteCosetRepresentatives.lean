import Mathlib
open scoped Topology

namespace GlobalTheory.CompanionTheory.OpenSubgroupCosets

/- English proof (translation)
Introduce `E _ _ _ D hD R hR`. Take `⟨t, ht⟩` from `hR.elim_finite_subcover (fun x : E => (fun y => y - x) ⁻¹' (D : Set E)) (fun x => hD.preimage (continuous_sub_right x)) (fun r _ => Set.mem_iUnion.2 ⟨r, by simp⟩)`. Use `set π : E → E ⧸ D := QuotientAddGroup.mk with hπ`. Establish `hfin : (π '' R).Finite`. Apply `(t.finite_toSet.image π).subset` to reduce the goal to its premises.

Introduce and unpack `_ ⟨r, hr, rfl⟩`. Take `⟨x, hx, hrx⟩ : ∃ x ∈ t, r - x ∈ D` from `by simpa using ht hr`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations. Apply `QuotientAddGroup.eq_iff_sub_mem.2` to reduce the goal to its premises. Rewrite using `[← neg_sub]`.

Conclude with `D.neg_mem hrx`. Establish `hrep : ∀ c ∈ π '' R, ∃ r, r ∈ R ∧ π r = c`. Introduce and unpack `_ ⟨r, hr, rfl⟩`. Conclude with `⟨r, hr, rfl⟩`. Use `choose! f hfR hfπ using hrep`.

Use `⟨hfin.toFinset.image f, ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs`. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.1 hs`. Conclude with `hfR c (hfin.mem_toFinset.1 hc)`. Introduce `x hx`.

Establish `hxc : π x ∈ π '' R` using `⟨x, hx, rfl⟩`. Use `⟨f (π x), ⟨Finset.mem_image.2 ⟨π x, hfin.mem_toFinset.2 hxc, rfl⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `QuotientAddGroup.eq_iff_sub_mem.1 (hfπ (π x) hxc).symm`. Introduce and unpack `s ⟨hs, hxs⟩`. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.1 hs`.

Establish `hc'` using `hfin.mem_toFinset.1 hc`. Establish `h1 : π x = c`. Rewrite using `[← hfπ c hc']`. Conclude with `QuotientAddGroup.eq_iff_sub_mem.2 hxs`. Rewrite using `[h1]`.
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
