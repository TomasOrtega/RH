import Mathlib

/- English proof (translation)
Introduce `α r hs _ t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩`. Consider the case `insert y s _ ih`. Take `⟨C, hC, h1, h2⟩` from `ih`.

Distinguish the cases in `h : ∃ c ∈ C, r y c`. Use `⟨C, hC.trans (Finset.subset_insert _ _), h1, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Conclude with `Or.inr h`.

Conclude with `h2 x hx`. Use `⟨insert y C, Finset.insert_subset_insert _ hC, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha b hb hab`. Break down `Finset.mem_insert.1 ha with ha | ha` into its components or cases. Break down `Finset.mem_insert.1 hb with hb | hb` into its components or cases.

Rewrite using `[ha, hb]`. Conclude with `absurd ⟨b, hb, ha ▸ hab⟩ h`. Break down `Finset.mem_insert.1 hb with hb | hb` into its components or cases. Conclude with `absurd ⟨a, ha, hb ▸ hs a b hab⟩ h`. Conclude with `h1 a ha b hb hab`.

Introduce `x hx`. Break down `Finset.mem_insert.1 hx with hx | hx` into its components or cases. Conclude with `Or.inl (Finset.mem_insert.2 (Or.inl hx))`. Break down `h2 x hx with h3 | ⟨c, hc, h3⟩` into its components or cases. Conclude with `Or.inl (Finset.mem_insert_of_mem h3)`.

Conclude with `Or.inr ⟨c, Finset.mem_insert_of_mem hc, h3⟩`.
-/
theorem UpperTheory.Reformulated.B.Rc5.exists_reps :
    ∀ {α : Type} (r : α → α → Prop),
    (∀ (a b : α), r a b → r b a) →
      (∀ (a b c : α), r a b → r b c → r a c) →
        ∀ (t : Finset α), ∃ C ⊆ t, (∀ a ∈ C, ∀ b ∈ C, r a b → a = b) ∧ ∀ x ∈ t, x ∈ C ∨ ∃ c ∈ C, r x c := by
  intro α r hs _ t
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
  | insert y s _ ih =>
    obtain ⟨C, hC, h1, h2⟩ := ih
    by_cases h : ∃ c ∈ C, r y c
    · refine ⟨C, hC.trans (Finset.subset_insert _ _), h1, ?_⟩
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Or.inr h
      · exact h2 x hx
    · refine ⟨insert y C, Finset.insert_subset_insert _ hC, ?_, ?_⟩
      · intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with ha | ha
        · rcases Finset.mem_insert.1 hb with hb | hb
          · rw [ha, hb]
          · exact absurd ⟨b, hb, ha ▸ hab⟩ h
        · rcases Finset.mem_insert.1 hb with hb | hb
          · exact absurd ⟨a, ha, hb ▸ hs a b hab⟩ h
          · exact h1 a ha b hb hab
      · intro x hx
        rcases Finset.mem_insert.1 hx with hx | hx
        · exact Or.inl (Finset.mem_insert.2 (Or.inl hx))
        · rcases h2 x hx with h3 | ⟨c, hc, h3⟩
          · exact Or.inl (Finset.mem_insert_of_mem h3)
          · exact Or.inr ⟨c, Finset.mem_insert_of_mem hc, h3⟩
