import Mathlib

namespace UpperTheory.Reformulated.B.P6.r08a

/- English proof (translation)
Introduce `K inst H T`. Use `Finset.induction_on T ?_ ?_` and prove the remaining obligations. Use `⟨∅, Finset.Subset.refl _, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Conclude with `absurd hx (Finset.notMem_empty x)`.

Introduce `r hr`. Conclude with `absurd hr (Finset.notMem_empty r)`. Introduce `a S _ha ih`. Take `⟨Rep, hsub, hcov, hsep⟩` from `ih`. Distinguish the cases in `h : ∃ r ∈ Rep, a - r ∈ H`.

Use `⟨Rep, hsub.trans (Finset.subset_insert a S), ?_, hsep⟩` and prove the remaining obligations. Introduce `x hx`. Break down `Finset.mem_insert.mp hx with hxa | hx` into its components or cases. Rewrite using `[hxa]`. Conclude with `h`.

Conclude with `hcov x hx`. Establish `h' : ∀ r ∈ Rep, a - r ∉ H` using `fun r hr har => h ⟨r, hr, har⟩`. Use `⟨insert a Rep, Finset.insert_subset_insert a hsub, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Break down `Finset.mem_insert.mp hx with hxa | hx` into its components or cases.

Use `⟨a, Finset.mem_insert_self a Rep, ?_⟩` and prove the remaining obligations. Rewrite using `[hxa, sub_self]`. Conclude with `H.zero_mem`. Take `⟨r, hr, hxr⟩` from `hcov x hx`. Conclude with `⟨r, Finset.mem_insert_of_mem hr, hxr⟩`.

Introduce `r hr r' hr' hrr`. Break down `Finset.mem_insert.mp hr with hra | hr` into its components or cases. Break down `Finset.mem_insert.mp hr' with hr'a | hr'` into its components or cases. Rewrite using `[hra, hr'a]`. Rewrite `hrr` using `[hra]`.

Conclude with `absurd hrr (h' r' hr')`. Break down `Finset.mem_insert.mp hr' with hr'a | hr'` into its components or cases. Rewrite `hrr` using `[hr'a]`. Establish `hn` using `H.neg_mem hrr`. Rewrite `hn` using `[neg_sub]`.

Conclude with `absurd hn (h' r hr)`. Conclude with `hsep r hr r' hr' hrr`.
-/
theorem GlobalTheory.CompanionTheory.AvgFree.Cov.exists_sep :
    ∀ {K : Type} [inst : AddCommGroup K] (H : AddSubgroup K) (T : Finset K), ∃ Rep ⊆ T, (∀ x ∈ T, ∃ r ∈ Rep, x - r ∈ H) ∧ ∀ r ∈ Rep, ∀ r' ∈ Rep, r - r' ∈ H → r = r' := by
  intro K inst H T
  classical
  refine Finset.induction_on T ?_ ?_
  · refine ⟨∅, Finset.Subset.refl _, ?_, ?_⟩
    · intro x hx
      exact absurd hx (Finset.notMem_empty x)
    · intro r hr
      exact absurd hr (Finset.notMem_empty r)
  · intro a S _ha ih
    obtain ⟨Rep, hsub, hcov, hsep⟩ := ih
    by_cases h : ∃ r ∈ Rep, a - r ∈ H
    · refine ⟨Rep, hsub.trans (Finset.subset_insert a S), ?_, hsep⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hx
      · rw [hxa]
        exact h
      · exact hcov x hx
    · have h' : ∀ r ∈ Rep, a - r ∉ H := fun r hr har => h ⟨r, hr, har⟩
      refine ⟨insert a Rep, Finset.insert_subset_insert a hsub, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with hxa | hx
        · refine ⟨a, Finset.mem_insert_self a Rep, ?_⟩
          rw [hxa, sub_self]
          exact H.zero_mem
        · obtain ⟨r, hr, hxr⟩ := hcov x hx
          exact ⟨r, Finset.mem_insert_of_mem hr, hxr⟩
      · intro r hr r' hr' hrr
        rcases Finset.mem_insert.mp hr with hra | hr
        · rcases Finset.mem_insert.mp hr' with hr'a | hr'
          · rw [hra, hr'a]
          · rw [hra] at hrr
            exact absurd hrr (h' r' hr')
        · rcases Finset.mem_insert.mp hr' with hr'a | hr'
          · rw [hr'a] at hrr
            have hn := H.neg_mem hrr
            rw [neg_sub] at hn
            exact absurd hn (h' r hr)
          · exact hsep r hr r' hr' hrr

end UpperTheory.Reformulated.B.P6.r08a
