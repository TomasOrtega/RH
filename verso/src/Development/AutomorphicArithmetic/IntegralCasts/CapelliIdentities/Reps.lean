import Mathlib

/- English proof (translation)
Introduce `α r hr A`. Proceed by induction on `A using Finset.induction_on with`. Consider the case `empty => exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩`. Consider the case `insert a s _ ih`. Take `⟨T, hTs, hinj, hcov⟩` from `ih`.

Distinguish the cases in `h : ∃ t ∈ T, r a t`. Use `⟨T, hTs.trans (Finset.subset_insert a s), hinj, ?_⟩` and prove the remaining obligations. Introduce `b hb`. Break down `Finset.mem_insert.mp hb with rfl | hb` into its components or cases. Conclude with `h`.

Conclude with `hcov b hb`. Use `⟨insert a T, Finset.insert_subset_insert a hTs, ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht t' ht' htt`. Break down `Finset.mem_insert.mp ht with h1 | h1` into its components or cases. Break down `Finset.mem_insert.mp ht' with h2 | h2` into its components or cases.

Rewrite using `[h1, h2]`. Conclude with `absurd ⟨t', h2, h1 ▸ htt⟩ h`. Break down `Finset.mem_insert.mp ht' with h2 | h2` into its components or cases. Conclude with `absurd ⟨t, h1, h2 ▸ hr.symm htt⟩ h`. Conclude with `hinj t h1 t' h2 htt`.

Introduce `b hb`. Break down `Finset.mem_insert.mp hb with h1 | h1` into its components or cases. Conclude with `⟨b, Finset.mem_insert.mpr (Or.inl h1), hr.refl b⟩`. Take `⟨t, ht, hbt⟩` from `hcov b h1`. Conclude with `⟨t, Finset.mem_insert_of_mem ht, hbt⟩`.
-/
theorem UpperTheory.Reformulated.B.Qh68.reps.{u_1} :
    ∀ {α : Type u_1} (r : α → α → Prop),
    Equivalence r → ∀ (A : Finset α), ∃ T ⊆ A, (∀ t ∈ T, ∀ t' ∈ T, r t t' → t = t') ∧ ∀ a ∈ A, ∃ t ∈ T, r a t := by
  intro α r hr A
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
  | insert a s _ ih =>
    obtain ⟨T, hTs, hinj, hcov⟩ := ih
    by_cases h : ∃ t ∈ T, r a t
    · refine ⟨T, hTs.trans (Finset.subset_insert a s), hinj, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact h
      · exact hcov b hb
    · refine ⟨insert a T, Finset.insert_subset_insert a hTs, ?_, ?_⟩
      · intro t ht t' ht' htt
        rcases Finset.mem_insert.mp ht with h1 | h1
        · rcases Finset.mem_insert.mp ht' with h2 | h2
          · rw [h1, h2]
          · exact absurd ⟨t', h2, h1 ▸ htt⟩ h
        · rcases Finset.mem_insert.mp ht' with h2 | h2
          · exact absurd ⟨t, h1, h2 ▸ hr.symm htt⟩ h
          · exact hinj t h1 t' h2 htt
      · intro b hb
        rcases Finset.mem_insert.mp hb with h1 | h1
        · exact ⟨b, Finset.mem_insert.mpr (Or.inl h1), hr.refl b⟩
        · obtain ⟨t, ht, hbt⟩ := hcov b h1
          exact ⟨t, Finset.mem_insert_of_mem ht, hbt⟩
